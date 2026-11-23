import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankEqZeroIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroup
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueCmEmbeddingEigenvectorSum
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EigenBasisIffTangentBasis
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LieBasisIffTangentBasisPullbackUniversal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj

namespace GlobalTheory.LocM.FrameBase

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem exists_tangent_module {X : Scheme.{0}} (t : SAB H X) {S : Type} [CommRing S] (x : Sp S ⟶ X) :
    ∃ (N : Type) (_ : AddCommGroup N) (_ : Module S N) (v : N → (Sp (DualNumber S) ⟶ t.G.left))
      (ρ : 𝓞 E →+* Module.End S N), Function.Injective v ∧ (∀ w, IsTanAtG t x w ↔ w ∈ Set.range v) ∧
      (∀ (n : ℕ) (b : Fin n → N) (a : Fin n → S) w,
        IsCombAtG t x (fun i => v (b i)) a w ↔ w = v (∑ i, a i • b i)) ∧
      (∀ a m, v (ρ a m) = v m ≫ (t.act.act a).left) ∧ ∀ (s : S) m, v (s • m) = spMap (epsMul s) ≫ v m := by
  have := t.semi.comm
  refine ⟨TanMod.TanSp x t.G, inferInstance, inferInstance, fun m => m.pt.left, TanMod.TanSp.act x t.act,
    fun m n h => TanMod.TanSp.ext (Over.OverMorphism.ext h), fun w => ⟨fun h => ?_, ?_⟩, fun n b a w => ⟨?_, ?_⟩,
    fun a m => rfl, fun s m => rfl⟩
  · exact ⟨TanMod.TanSp.mk (Over.homMk w h.1) (TanMod.smT_zero_of x _ h.2), rfl⟩
  · rintro ⟨m, rfl⟩
    exact ⟨Over.w m.pt, TanMod.unit_of_smT_zero x _ m.tan⟩
  · rintro ⟨u, hu, rfl⟩
    have : u = fun i => (a i • b i).pt := funext fun i => Over.OverMorphism.ext (hu i)
    subst this
    rw [List.prod_ofFn, ← TanMod.TanSp.pt_sum]
  · rintro rfl
    exact ⟨fun i => (a i • b i).pt, fun i => rfl, by rw [List.prod_ofFn, ← TanMod.TanSp.pt_sum]⟩

theorem eigBasis_iff {Dw : Datum H} {l : Level H} (c : Coeff l) {X : Scheme.{0}} (t : SAB H X) {S : Type} [CommRing S]
    (f : c.F →+* S) (x : Sp S ⟶ X) (u : Vecs Dw t S) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (ht : ∀ τ i, IsTanAtG t x (u τ i))
    (he : ∀ τ i (a : 𝓞 E), u τ i ≫ (t.act.act a).left = spMap (epsMul (f (embK c τ a))) ≫ u τ i) :
    (∀ τ w, IsTanAtG t x w → (∀ a : 𝓞 E, w ≫ (t.act.act a).left = spMap (epsMul (f (embK c τ a))) ≫ w) →
      ∃! a : Fin (Dw.mult τ) → S, IsCombAtG t x (u τ) a w) ↔
    ∀ w, IsTanAtG t x w → ∃! a : Fin g → S, IsCombAtG t x (fun j => u (e j).1 (e j).2) a w := by
  let _ : Algebra c.F S := f.toAlgebra
  obtain ⟨N, _, _, v, ρ, hinj, htan, hcomb, hρ, hsm⟩ := exists_tangent_module t x
  choose b hb using fun τ i => (htan (u τ i)).1 (ht τ i)
  obtain rfl : u = fun τ i => v (b τ i) := by funext τ i; exact (hb τ i).symm
  let M : (E →+* ℂ) → Submodule S N := fun τ =>
    ⨅ a : 𝓞 E, Module.End.eigenspace (ρ a) (f (embK c τ a))
  have hM : ∀ τ n, n ∈ M τ ↔ ∀ a, ρ a n = f (embK c τ a) • n := by
    intro τ n
    simp only [M, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  have hE : ∀ τ n, (∀ a : 𝓞 E, v n ≫ (t.act.act a).left = spMap (epsMul (f (embK c τ a))) ≫ v n) ↔ n ∈ M τ := by
    intro τ n
    rw [hM]
    refine forall_congr' fun a => ?_
    rw [← hρ, ← hsm, hinj.eq_iff]
  have hs : ∀ n : N, ∃! f : (E →+* ℂ) → N, (∀ τ, f τ ∈ M τ) ∧ ∑ τ, f τ = n := by
    intro n
    simp only [hM]
    exact GlobalTheory.Frames.existsUnique_eigen_sum E H l c S N ρ n
  have hmain := GlobalTheory.Frames.basis_iff_of_split (fun τ => Dw.mult τ) M hs b (fun τ i => (hE τ _).1 (he τ i)) g e
  have hT : ∀ n, IsTanAtG t x (v n) := fun n => (htan _).2 ⟨n, rfl⟩
  have hC : ∀ (k : ℕ) (b : Fin k → N) (a : Fin k → S) (n : N),
      IsCombAtG t x (fun i => v (b i)) a (v n) ↔ n = ∑ i, a i • b i := by
    intro k b a n
    rw [hcomb, hinj.eq_iff]
  constructor
  · intro h w hw
    obtain ⟨n, rfl⟩ := (htan w).1 hw
    have h1 := hmain.1 (fun τ n hn => by
      have h2 := h τ (v n) (hT n) ((hE τ n).2 hn)
      simpa only [hC] using h2) n
    simpa only [hC] using h1
  · intro h τ w hw hew
    obtain ⟨n, rfl⟩ := (htan w).1 hw
    have h1 := hmain.2 (fun n => by
      have h2 := h (v n) (hT n)
      simpa only [hC] using h2) τ n ((hE τ n).1 hew)
    simpa only [hC] using h1

theorem lieBasis_iff {X : Scheme.{0}} (t : SAB H X) {S : Type} [CommRing S] (x : Sp S ⟶ X) (G' : Over (Sp S)) [GrpObj G']
    (φ : G'.left ⟶ t.G.left) (hp : IsGrpPullback G' t.G x φ) :
    (∀ w : (Sp (DualNumber S) ⟶ t.G.left), IsTanAtG t x w → ∃ v : epsR S ⟶ G', v.left ≫ φ = w) ∧
    ∀ (n : ℕ) (v : Fin n → (epsR S ⟶ G')), IsLieBasis v ↔ ((∀ i, IsTanAtG t x ((v i).left ≫ φ)) ∧
      ∀ w, IsTanAtG t x w → ∃! a : Fin n → S, IsCombAtG t x (fun i => (v i).left ≫ φ) a w) := by
  let up : ∀ w : Sp (DualNumber S) ⟶ t.G.left,
      w ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x → (epsR S ⟶ G') :=
    fun w h => Over.homMk (hp.1.lift w _ h) (hp.1.lift_snd _ _ _)
  have hup : ∀ w h, (up w h).left ≫ φ = w := fun w h => hp.1.lift_fst _ _ _
  have inj : ∀ {T : Over (Sp S)} {u v : T ⟶ G'}, u.left ≫ φ = v.left ≫ φ → u = v := fun h =>
    Over.OverMorphism.ext (hp.1.hom_ext h ((Over.w _).trans (Over.w _).symm))
  have one : ∀ T : Over (Sp S), (1 : T ⟶ G').left ≫ φ = (1 : Over.mk (T.hom ≫ x) ⟶ t.G).left :=
    fun T => congrArg (fun q => q.left) (map_one (pushHom hp T))
  have e : η[G'].left ≫ φ = (1 : Over.mk x ⟶ t.G).left := by
    have e₁ : (1 : 𝟙_ (Over (Sp S)) ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
    rw [← e₁, one]
    exact congrArg (· ≫ (η[t.G]).left) (Category.id_comp x)
  have zs : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
    have e : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S := by
      ext s; simp
    simp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
    simp
  have tan : ∀ w : epsR S ⟶ G', IsTangent w ↔ IsTanAtG t x (w.left ≫ φ) := fun w => by
    refine ⟨fun h => ⟨Over.w (pushPt hp.1.w w), ?_⟩, fun h => hp.1.hom_ext ?_ ?_⟩
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q ≫ φ) h).trans e)
    · exact (Category.assoc _ _ _).trans (h.2.trans e.symm)
    · refine (Category.assoc _ _ _).trans ?_
      rw [Over.w w, Over.w η[G']]
      exact zs
  have pr : ∀ {n} (u : Fin n → (epsR S ⟶ G')), (List.ofFn u).prod.left ≫ φ =
      (List.ofFn fun i => (pushPt hp.1.w (u i) : tEpsG x ⟶ t.G)).prod.left := fun u =>
    congrArg (fun q => q.left) ((map_list_prod (pushHom hp (epsR S)) _).trans (by rw [List.map_ofFn]; rfl))
  have comb : ∀ {n} (c : Fin n → S) (v : Fin n → (epsR S ⟶ G')) w,
      IsLieComb c v w ↔ IsCombAtG t x (fun i => (v i).left ≫ φ) c (w.left ≫ φ) := fun c v w => by
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun i => pushPt hp.1.w (u i), fun i => (congrArg (· ≫ φ) (hu i)).trans (Category.assoc _ _ _), (pr u).symm⟩
    · rintro ⟨u, hu, hw⟩
      refine ⟨fun i => up (u i).left (Over.w _), fun i => hp.1.hom_ext ?_ ?_,
        inj (hw.symm.trans (Eq.trans ?_ (pr _).symm))⟩
      · exact (hup _ _).trans ((hu i).trans (Category.assoc _ _ _).symm)
      · refine (Over.w (up (u i).left (Over.w _))).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
        refine Eq.trans ?_ (congrArg (spMap (epsScaleR (c i)) ≫ ·) (Over.w (v i))).symm
        exact (GlobalTheory.Frames.spMap_epsScaleR_comp (c i)).symm
      · have : u = fun i => (pushPt hp.1.w (up (u i).left (Over.w _)) : tEpsG x ⟶ t.G) :=
          funext fun i => Over.OverMorphism.ext (hup (u i).left (Over.w _)).symm
        exact congrArg (fun q : _ → (tEpsG x ⟶ t.G) => (List.ofFn q).prod.left) this
  refine ⟨fun w hw => ⟨up w hw.1, hup _ _⟩, fun n v => ⟨fun hB => ⟨fun i => (tan _).1 (hB.1 i), fun w hw => ?_⟩,
    fun hB => ⟨fun i => (tan _).2 (hB.1 i), fun w hw => ?_⟩⟩⟩
  · have h := hB.2 (up w hw.1) ((tan _).2 (by rw [hup]; exact hw))
    simp only [comb, hup] at h
    exact h
  · have h := hB.2 _ ((tan _).1 hw)
    simp only [comb]
    exact h

theorem tanBasis_baseChange {X : Scheme.{0}} (t : SAB H X) {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T)
    (x : Sp S ⟶ X) (n : ℕ) (v : Fin n → (Sp (DualNumber S) ⟶ t.G.left)) (hv : ∀ i, IsTanAtG t x (v i))
    (hv' : ∀ w, IsTanAtG t x w → ∃! a : Fin n → S, IsCombAtG t x v a w) :
    (∀ i, IsTanAtG t (spMap φ ≫ x) (spMap (dualMap φ) ≫ v i)) ∧
      ∀ w, IsTanAtG t (spMap φ ≫ x) w →
        ∃! a : Fin n → T, IsCombAtG t (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ v i) a w := by
  have := t.semi.comm
  have := t.semi.smooth
  have h₁ := isGrpPullback_pullback t.G x
  have h₂ := isGrpPullback_pullback ((Over.pullback x).obj t.G) (spMap φ)
  have h₃ := h₂.comp h₁
  have : IsCommMonObj ((Over.pullback x).obj t.G) := Functor.isCommMonObj_obj
  have : IsCommMonObj ((Over.pullback (spMap φ)).obj ((Over.pullback x).obj t.G)) :=
    Functor.isCommMonObj_obj
  obtain ⟨a₁, b₁⟩ := lieBasis_iff t x _ _ h₁
  obtain ⟨-, b₃⟩ := lieBasis_iff t _ _ _ h₃
  choose u hu using fun i => a₁ (v i) (hv i)
  have hb : IsLieBasis u := (b₁ n u).2 ⟨fun i => by rw [hu]; exact hv i, by rw [funext hu]; exact hv'⟩
  have hs : Smooth ((Over.pullback x).obj t.G).hom :=
    inferInstanceAs (Smooth (pullback.snd t.G.hom x))
  obtain ⟨u', hb', hu'⟩ := GlobalTheory.exists_isLieBasis_baseChange S T φ _ _ _ h₂ hs n u hb
  have e : Chart.dualMapR φ = dualMap φ := by
    ext a <;> rfl
  have key := (b₃ n u').1 hb'
  have e' : ∀ i, (u' i).left ≫ pullback.fst ((Over.pullback x).obj t.G).hom (spMap φ) ≫ pullback.fst t.G.hom x =
      spMap (dualMap φ) ≫ v i := fun i => by
    rw [← Category.assoc, hu', e, Category.assoc, hu]
  refine ⟨fun i => e' i ▸ key.1 i, ?_⟩
  rw [← funext e']
  exact key.2

theorem spMap_dualMap_epsMul {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (a : S) :
    spMap (dualMap ψ) ≫ spMap (epsMul a) = spMap (epsMul (ψ a)) ≫ spMap (dualMap ψ) := by
  rw [TanMod.spMap_comp', TanMod.spMap_comp']
  congr 1
  refine RingHom.ext fun z => ?_
  ext <;> simp [dualMap, epsMul, mul_comm]

theorem frameBase : GlobalTheory.LocM.Cht.FrameBaseSt := by
  intro E _ _ _ H Dw l c X t R R' _ _ f x φ u h
  let e := (Fintype.equivFin (Σ τ : E →+* ℂ, Fin (Dw.mult τ))).symm
  have h1 := (eigBasis_iff c t f x u _ e (fun τ i => (h.1 τ i).1) (fun τ i => (h.1 τ i).2)).1 h.2
  obtain ⟨h2, h3⟩ := tanBasis_baseChange t φ x _ _ (fun j => (h.1 (e j).1 (e j).2).1) h1
  have ht : ∀ τ i, IsTanAtG t (spMap φ ≫ x) (u.bc φ τ i) := fun τ i => by
    have := h2 (e.symm ⟨τ, i⟩)
    rw [Equiv.apply_symm_apply] at this
    exact this
  have he : ∀ τ i (a : 𝓞 E), u.bc φ τ i ≫ (t.act.act a).left =
      spMap (epsMul ((φ.comp f) (embK c τ a))) ≫ u.bc φ τ i := fun τ i a => by
    rw [Vecs.bc, Category.assoc, (h.1 τ i).2 a, ← Category.assoc, spMap_dualMap_epsMul, Category.assoc, RingHom.comp_apply]
  exact ⟨fun τ i => ⟨ht τ i, he τ i⟩, (eigBasis_iff c t (φ.comp f) _ (u.bc φ) _ e ht he).2 h3⟩

end GlobalTheory.LocM.FrameBase
