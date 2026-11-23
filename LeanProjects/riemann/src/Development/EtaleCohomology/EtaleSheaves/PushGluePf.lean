import Development.EtaleCohomology.EtaleSheaves.CokernelKilling.KillCokOf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.KillCokPf.Asm
open scoped TensorProduct

namespace LateralTheory.E.PushGluePf

abbrev pS (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) :
    H R (sch.obj (Spec A)) F n →+ H R (sch.obj (Spec B)) F n :=
  pull R (sch.map (Spec.map f)) F n

theorem pS_comp (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C)
    (x : H R (sch.obj (Spec A)) F n) : pS R F n (f ≫ g) x = pS R F n g (pS R F n f x) := by
  simp only [pS]; rw [Spec.map_comp, Functor.map_comp, pull_comp]

abbrev ev {ι : Type} (Y : ι → CommRingCat.{0}) (j : ι) : CommRingCat.of (∀ k, Y k) ⟶ Y j :=
  CommRingCat.ofHom (Pi.evalRingHom (fun k => Y k) j)

theorem pull_iso_bij (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {E E' : Spc} (g : E ⟶ E') [IsIso g] :
    Function.Bijective (pull R g F n) := by
  have h1 : ∀ x, pull R (inv g) F n (pull R g F n x) = x := fun x => by
    rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  have h2 : ∀ x, pull R g F n (pull R (inv g) F n x) = x := fun x => by
    rw [← pull_comp, IsIso.hom_inv_id, pull_id]
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

theorem pi_bij (hC : Coprod) (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {ι : Type} [Finite ι]
    (Y : ι → CommRingCat.{0}) :
    Function.Bijective fun (x : H R (sch.obj (Spec (CommRingCat.of (∀ k, Y k)))) F n) (j : ι) => pS R F n (ev Y j) x := by
  have h : (fun (x : H R (sch.obj (Spec (CommRingCat.of (∀ k, Y k)))) F n) (j : ι) => pS R F n (ev Y j) x) =
      (fun (x : H R (sch.obj (∐ fun k => Spec (Y k))) F n) (j : ι) =>
        pull R (sch.map (Sigma.ι (fun k => Spec (Y k)) j)) F n x) ∘ pull R (sch.map (sigmaSpec Y)) F n := by
    funext x j
    simp only [Function.comp_apply, pS, ev]
    rw [← pull_comp, ← Functor.map_comp, ι_sigmaSpec]
  rw [h]
  exact (hC R F (fun k => Spec (Y k)) n).comp (pull_iso_bij R F n _)

theorem pushout_pi {D Y' : CommRingCat.{0}} (φ' : D ⟶ Y') {ι : Type} [Fintype ι] (D₁ : ι → CommRingCat.{0})
    (e : ∀ k, D ⟶ D₁ k) (Y₁ : ι → CommRingCat.{0}) (u : ∀ k, Y' ⟶ Y₁ k) (φ₁ : ∀ k, D₁ k ⟶ Y₁ k)
    (hpo : ∀ k, IsPushout φ' (e k) (u k) (φ₁ k)) :
    IsPushout φ' (piMap D₁ e) (CommRingCat.ofHom (Pi.ringHom fun k => (u k).hom))
      (CommRingCat.ofHom (Pi.ringHom fun k => (φ₁ k).hom.comp (Pi.evalRingHom (fun k => D₁ k) k))) := by
  classical
  letI : Algebra D Y' := φ'.hom.toAlgebra
  letI : ∀ k, Algebra D (D₁ k) := fun k => (e k).hom.toAlgebra
  have hT : IsPushout φ' (piMap D₁ e) _ _ := CommRingCat.isPushout_tensorProduct D Y' (∀ k, D₁ k)
  have hTk : ∀ k, IsPushout φ' (e k) _ _ := fun k => CommRingCat.isPushout_tensorProduct D Y' (D₁ k)
  let isk : ∀ k, CommRingCat.of (Y' ⊗[D] D₁ k) ≅ Y₁ k := fun k => IsPushout.isoIsPushout _ _ (hTk k) (hpo k)
  have hl : ∀ k (y : Y'), (isk k).hom (y ⊗ₜ 1) = u k y := fun k y => by
    have := IsPushout.inl_isoIsPushout_hom _ _ (hTk k) (hpo k)
    exact congrArg (fun f => f.hom y) this
  have hr : ∀ k (d : D₁ k), (isk k).hom (1 ⊗ₜ d) = φ₁ k d := fun k d => by
    have := IsPushout.inr_isoIsPushout_hom _ _ (hTk k) (hpo k)
    exact congrArg (fun f => f.hom d) this
  let e₄ : CommRingCat.of (Y' ⊗[D] (∀ k, D₁ k)) ≅ CommRingCat.of (∀ k, Y₁ k) :=
    ((Algebra.TensorProduct.piRight D D Y' (fun k => D₁ k)).toRingEquiv.trans
      (RingEquiv.piCongrRight fun k => (isk k).commRingCatIsoToRingEquiv)).toCommRingCatIso
  refine hT.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e₄ (by simp) (by simp) ?_ ?_
  · refine CommRingCat.hom_ext (RingHom.ext fun y => funext fun k => ?_)
    have h4 : e₄.hom (y ⊗ₜ (1 : ∀ k, D₁ k)) k = (isk k).hom (y ⊗ₜ 1) := by
      simp [e₄, Algebra.TensorProduct.piRight_tmul]; rfl
    exact h4.trans (hl k y)
  · refine CommRingCat.hom_ext (RingHom.ext fun d => funext fun k => ?_)
    have h4 : e₄.hom ((1 : Y') ⊗ₜ d) k = (isk k).hom (1 ⊗ₜ d k) := by
      simp [e₄, Algebra.TensorProduct.piRight_tmul]; rfl
    exact h4.trans (hr k (d k))

theorem PushGlue_of (hC : Coprod) : LateralTheory.E.KillCokPf.Glue.PushGlue := by
  intro _ q _ i D Y' φ' m y ι _ D₁ e _ hk
  classical
  choose Y₁ u φ₁ hpo hz using hk
  choose z hz using hz
  obtain ⟨z₀, hz₀⟩ := (pi_bij hC (ZMod q) (tw q i) m D₁).2 z
  have hz₀' : ∀ j, pS _ (tw q i) m (ev D₁ j) z₀ = z j := fun j => congrFun hz₀ j
  let u'' : Y' ⟶ CommRingCat.of (∀ k, Y₁ k) := CommRingCat.ofHom (Pi.ringHom fun k => (u k).hom)
  let φ'' : CommRingCat.of (∀ k, D₁ k) ⟶ CommRingCat.of (∀ k, Y₁ k) :=
    CommRingCat.ofHom (Pi.ringHom fun k => (φ₁ k).hom.comp (Pi.evalRingHom (fun k => D₁ k) k))
  refine ⟨CommRingCat.of (∀ k, Y₁ k), u'', φ'', ?_, z₀, ?_⟩
  · exact pushout_pi φ' D₁ e Y₁ u φ₁ hpo
  · apply (pi_bij hC (ZMod q) (tw q i) m Y₁).1
    funext j
    have e1 : φ'' ≫ ev Y₁ j = ev D₁ j ≫ φ₁ j := rfl
    have e2 : u'' ≫ ev Y₁ j = u j := rfl
    show pS _ (tw q i) m (ev Y₁ j) (pS _ (tw q i) m φ'' z₀) = pS _ (tw q i) m (ev Y₁ j) (pS _ (tw q i) m u'' y)
    rw [← pS_comp, ← pS_comp, e1, e2, pS_comp, hz₀']
    exact hz j

end LateralTheory.E.PushGluePf
