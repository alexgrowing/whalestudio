import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FiniteDegreeMorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameOfProjective
open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CurveRootGeometry.EigenSeq

section Eigen

variable {X : Scheme.{0}} {O : Type} [CommRing O] {k : Type} [Field k] [Algebra k Γ(X, ⊤)]
  {κ : Type} {τ : κ → (O →+* k)}

theorem tensorAct_comp {F G : X.Modules} {ρ : O →+* End F} {ρ' : O →+* End G} {φ : F ⟶ G}
    (h : IsEquivariant ρ ρ' φ) (x : TensorProduct ℤ k O) :
    act (tensorAct k ρ) x ≫ φ = φ ≫ act (tensorAct k ρ') x := by
  induction x with
  | zero => simp only [act, map_zero]; rw [zero_comp, comp_zero]
  | tmul c a => rw [act_tensorAct_tmul, act_tensorAct_tmul, Linear.smul_comp, Linear.comp_smul, h a]
  | add x y hx hy =>
    simp only [act, map_add] at hx hy ⊢
    rw [Preadditive.add_comp, Preadditive.comp_add, hx, hy]

variable [DecidableEq κ] (hτ : IsSplitBy τ)
include hτ

theorem proj_eigenMap {F G : X.Modules} {ρ : O →+* End F} {ρ' : O →+* End G} {φ : F ⟶ G}
    (h : IsEquivariant ρ ρ' φ) (j : κ) :
    hτ.proj ρ j ≫ eigenMap (scal X (τ j)) h = φ ≫ hτ.proj ρ' j := by
  rw [← cancel_mono (eigenι ρ' (scal X (τ j))), Category.assoc, eigenMap_ι, ← Category.assoc,
    IsSplitBy.proj_ι, Category.assoc, IsSplitBy.proj_ι, tensorAct_comp h]

theorem epi_proj {F : X.Modules} (ρ : O →+* End F) (j : κ) : Epi (hτ.proj ρ j) :=
  epi_of_epi_fac (hτ.ι_proj ρ j)

omit [DecidableEq κ] in

theorem shortExact_eigen [Fintype κ] {A B E : X.Modules} {ρA : O →+* End A} {ρB : O →+* End B}
    {ρE : O →+* End E} {f : A ⟶ B} {g : B ⟶ E} (hf : IsEquivariant ρA ρB f)
    (hg : IsEquivariant ρB ρE g) (w : f ≫ g = 0) (hS : (ShortComplex.mk f g w).ShortExact)
    (σ : O →+* k) (w' : eigenMap (scal X σ) hf ≫ eigenMap (scal X σ) hg = 0) :
    (ShortComplex.mk _ _ w').ShortExact := by
  classical
  obtain ⟨j, rfl⟩ := hτ.exists_eq σ
  have := hS.mono_f
  have := hS.epi_g
  have := epi_proj hτ ρE j
  let ι : ShortComplex.mk _ _ w' ⟶ ShortComplex.mk f g w :=
    { τ₁ := eigenι _ _, τ₂ := eigenι _ _, τ₃ := eigenι _ _
      comm₁₂ := (eigenMap_ι _ hf).symm, comm₂₃ := (eigenMap_ι _ hg).symm }
  let π : ShortComplex.mk f g w ⟶ ShortComplex.mk _ _ w' :=
    { τ₁ := hτ.proj ρA j, τ₂ := hτ.proj ρB j, τ₃ := hτ.proj ρE j
      comm₁₂ := proj_eigenMap hτ hf j, comm₂₃ := proj_eigenMap hτ hg j }
  have hιπ : ι ≫ π = 𝟙 _ := by
    ext <;> simp [ι, π]
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero,
      ← ShortComplex.homologyMap_id, ← hιπ, ShortComplex.homologyMap_comp,
      (ShortComplex.exact_iff_isZero_homology _).1 hS.exact |>.eq_zero_of_tgt (ShortComplex.homologyMap ι),
      zero_comp]
  · exact mono_of_mono_fac (eigenMap_ι _ hf)
  · exact epi_of_epi_fac (proj_eigenMap hτ hg j)

end Eigen

theorem isExtension_of_iso {X : Scheme.{0}} {A A' H B B' : X.Modules} (α : A ≅ A') (β : B' ≅ B)
    {f : A' ⟶ H} {g : H ⟶ B'} {w : f ≫ g = 0} (hS : (ShortComplex.mk f g w).ShortExact) :
    IndefiniteRowSideFullHecke.FrobeniusTwistEigen.IsExtension A H B := by
  refine ⟨α.hom ≫ f, g ≫ β.hom, by simp [reassoc_of% w], ShortComplex.shortExact_of_iso ?_ hS⟩
  exact ShortComplex.isoMk α.symm (Iso.refl _) β (by simp) (by simp)

end GlobalTheory.CurveRootGeometry.EigenSeq

namespace GlobalTheory.CurveRootGeometry.EigenSeq

theorem hasSeq_of_hasDieu : ∀ (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharP k q] (O : Type) [CommRing O], Splits O k →
  ∀ (c : O →+* O), Function.Involutive c → ∀ (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] [IsIntegral C], IsSmoothProjCurve k C →
  ∀ (G : Over C) [GrpObj G] [IsSemiAbelian G] (i : OAct O G), HasDieu q k c i → HasSeq q k c i := by
  intro q _ k _ _ _ O _ hs c hc C _ _ _ G _ _ i hD
  classical
  obtain ⟨κ, _, τ, hτ⟩ := hs
  obtain ⟨D, g, ρ, a, b, u, v, w₁, w₂, hω, hDv, hab, huv, ea, eb, eu, ev⟩ := hD
  have h0 := natCast_eq_zero C q k
  have hL : IsVB (Lie G) g := hω.dual
  have cc (σ : O →+* k) : (σ.comp c).comp c = σ := RingHom.ext fun x => congrArg σ (hc x)
  have vbL (σ : O →+* k) : ∃ r, IsVB (lieSub i (scal C σ)) r := by
    obtain ⟨j, rfl⟩ := hτ.exists_eq σ
    exact ⟨_, GlobalTheory.VB.isVB_of_retract C _ _ (eigenι _ _) (hτ.proj (lieAct i) j) g (hτ.ι_proj _ j) hL⟩
  have vbH (σ : O →+* k) : ∃ r, IsVB (eigen ρ (scal C σ)) r := by
    obtain ⟨j, rfl⟩ := hτ.exists_eq σ
    exact ⟨_, GlobalTheory.VB.isVB_of_retract C _ _ (eigenι _ _) (hτ.proj ρ j) (2 * g) (hτ.ι_proj _ j) hDv⟩
  choose rL hrL using vbL
  choose rH hrH using vbH
  refine ⟨fun σ => eigen ρ (scal C σ), rL, rH, D, g, hrL, hrH, fun σ => ?_, fun σ => ?_, hL, hDv, ?_,
    ⟨u, huv.mono_f⟩, ?_⟩
  · obtain ⟨j, rfl⟩ := hτ.exists_eq σ
    exact isExtension_of_iso (omegaSubIsoOfSplit i hτ hω j).symm (eigenConjIso (lieAct i) (scal C (τ j)) hc)
      (shortExact_eigen hτ ea eb w₁ hab (τ j) (by
        rw [← cancel_mono (eigenι _ _)]; simp [w₁]))
  · obtain ⟨j, rfl⟩ := hτ.exists_eq σ
    have := hτ.isIso_frobEigenHom q h0 ((lieAct i).comp c) j
    have := hτ.isIso_frobEigenHom q h0 (omegaAct i) j
    exact isExtension_of_iso
      ((frobPull q h0).mapIso (eigenConjIso (lieAct i) (scal C (τ j)) hc).symm ≪≫
        asIso (frobEigenHom q h0 ((lieAct i).comp c) (τ j)))
      ((asIso (frobEigenHom q h0 (omegaAct i) (τ j))).symm ≪≫ (frobPull q h0).mapIso (omegaSubIsoOfSplit i hτ hω j))
      (shortExact_eigen hτ eu ev w₂ huv ((frobenius k q).comp (τ j)) (by
        rw [← cancel_mono (eigenι _ _)]; simp [w₂]))
  · exact isExtension_of_iso (omegaIsoDualLie hω).symm (Iso.refl _) hab
  · have : Finite (O →+* k) := Finite.of_surjective τ hτ.exists_eq
    have : HasBiproduct fun j => eigen (lieAct i) (scal C (τ j)) := HasBiproduct.of_hasCoproduct _
    let e : κ ≃ (O →+* k) := Equiv.ofBijective (fun j => (τ j).comp c)
      ⟨fun j j' h => hτ.injective (by
        rw [← cc (τ j), ← cc (τ j')]; exact congrArg (fun σ : O →+* k => σ.comp c) h),
        fun σ => (hτ.exists_eq (σ.comp c)).imp fun j h => by
          show (τ j).comp c = σ
          rw [h, cc]⟩
    exact ⟨hτ.decompose (lieAct i) ≪≫ biproduct.isoCoproduct _ ≪≫
      Sigma.whiskerEquiv e fun j => eqToIso (by
        show lieSub i (scal C (((τ j).comp c).comp c)) = eigen (lieAct i) (scal C (τ j))
        rw [cc])⟩

end GlobalTheory.CurveRootGeometry.EigenSeq
