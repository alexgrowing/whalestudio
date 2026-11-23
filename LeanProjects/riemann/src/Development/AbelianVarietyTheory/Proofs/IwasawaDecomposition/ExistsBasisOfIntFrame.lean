import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.LieMet GlobalTheory.LocM
open GlobalTheory.GradedPieces GlobalTheory.Points

namespace GlobalTheory.TotalFrame

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_basis_sigma {O S M J : Type} [CommRing O] [CommRing S] [AddCommGroup M] [Module S M] [Fintype J]
    {χ : J → O →+* S} (h : EigenSplit.IsSplitting χ) (ρ : O →+* Module.End S M) {m : J → ℕ}
    (u : ∀ σ, Fin (m σ) → M) (li : ∀ σ, LinearIndependent S (u σ))
    (hs : ∀ σ, Submodule.span S (Set.range (u σ)) = EigenSplit.eigenSub ρ (χ σ)) :
    ∃ b : Module.Basis (Σ σ, Fin (m σ)) S M, ∀ σ a, b ⟨σ, a⟩ = u σ a := by
  classical
  have hi := EigenSplit.isInternal_eigenSub h ρ
  simp only [← hs] at hi
  exact ⟨hi.collectedBasis fun σ => Module.Basis.span (li σ), fun σ a => by
    rw [DirectSum.IsInternal.collectedBasis_coe]
    exact congrArg Subtype.val (Module.Basis.span_apply (li σ) a)⟩

section Tangent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ X} {m : ℕ}

theorem exists_basis {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} (hv : ∀ i, IsTanAtG t x (v i))
    (hb : ∀ w, IsTanAtG t x w → ∃! cf, IsCombAtG t x v cf w) :
    ∃ b : Module.Basis (Fin m) S (TanM x t.G), ∀ i, b i = tanOf (hv i) := by
  refine ⟨Module.Basis.mk (v := fun i => tanOf (hv i)) (Fintype.linearIndependent_iffₛ.2 fun c c' h => congrFun
    ((hb _ (isTan_tv (∑ i, c i • tanOf (hv i)))).unique ((isComb_iff (fun i => tanOf (hv i)) c _).2 rfl)
      ((isComb_iff (fun i => tanOf (hv i)) c' _).2 h))) fun w _ => ?_, fun i => Module.Basis.mk_apply _ _ i⟩
  obtain ⟨a, ha, -⟩ := hb _ (isTan_tv w)
  rw [(isComb_iff (fun i => tanOf (hv i)) a w).1 ha]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem exists_basis_map {J : Type} [Fintype J] (b : Module.Basis J S (TanM x t.G)) (φ : S →+* T) {x' : Sp T ⟶ X}
    (hx : spMap φ ≫ x = x') :
    ∃ b' : Module.Basis J T (TanM x' t.G), ∀ i, (tv (b' i)).left = spMap (dualMap φ) ≫ (tv (b i)).left := by
  let e := Fintype.equivFin J
  have hb : ∀ w, IsTanAtG t x w → ∃! cf, IsCombAtG t x (fun i => (tv (b.reindex e i)).left) cf w := fun w hw =>
    ⟨(b.reindex e).repr (tanOf hw), (isComb_iff _ _ (tanOf hw)).2 ((b.reindex e).sum_repr _).symm, fun a ha => by
      rw [(isComb_iff _ _ (tanOf hw)).1 ha, Module.Basis.repr_sum_self]⟩
  obtain ⟨b', hb'⟩ := exists_basis (fun i => isTan_map φ hx (isTan_tv (b.reindex e i)))
    (basis_map φ hx (fun i => isTan_tv _) hb)
  refine ⟨b'.reindex e.symm, fun i => ?_⟩
  rw [Module.Basis.reindex_apply, hb', left_tanOf, Module.Basis.reindex_apply, Equiv.symm_symm, Equiv.symm_apply_apply]

theorem dualMap_epsMul (φ : S →+* T) (a : S) {Y : Scheme.{0}} (v : Sp (DualNumber S) ⟶ Y) :
    spMap (dualMap φ) ≫ spMap (epsMul a) ≫ v = spMap (epsMul (φ a)) ≫ spMap (dualMap φ) ≫ v := by
  rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap]
  congr 2
  refine RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap, epsMul, mul_comm]

variable {Dw : Datum H} {l : Level H} {c : Coeff l} {w : Vecs Dw t S} {χ : (E →+* ℂ) → 𝓞 E →+* S}

variable (c x w χ) in

def FramesSeparate : Prop :=
  ∀ r s : S, (∀ (k : Type) [Field k] (φ : S →+* k) (f : c.F →+* k), IsFrame t f (spMap φ ≫ x) (w.bc φ) →
    (∀ σ a, f (embK c σ a) = φ (χ σ a)) → φ r = φ s) → r = s

theorem span_eq_eigenSub (hw : FramesSeparate x c w χ) (σ : E →+* ℂ) (ht : ∀ i, IsTanAtG t x (w σ i))
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} (e : Fin (Dw.mult σ) ↪ Fin m) (he : ∀ i, v (e i) = w σ i)
    (hv : ∀ i, IsTanAtG t x (v i)) (hb : ∀ u, IsTanAtG t x u → ∃! cf, IsCombAtG t x v cf u) :
    Submodule.span S (Set.range fun i => tanOf (ht i)) = EigenSplit.eigenSub (actR t.act) (χ σ) := by
  classical
  refine le_antisymm (Submodule.span_le.2 ?_) fun u hu => ?_
  · rintro _ ⟨i, rfl⟩
    refine EigenSplit.mem_eigenSub.2 fun a => ?_
    obtain ⟨g, hc, -⟩ := hb _ (isTan_tv (actR t.act a (tanOf (ht i))))
    obtain ⟨g', hc', -⟩ := hb _ (isTan_tv (χ σ a • tanOf (ht i)))
    have hcc : g = g' := funext fun l => hw _ _ fun k _ φ f hf hfj => by
      have h1 := comb_map φ rfl hc
      have h2 := comb_map φ rfl hc'
      have h3 : spMap (dualMap φ) ≫ (tv (actR t.act a (tanOf (ht i)))).left =
          spMap (dualMap φ) ≫ (tv (χ σ a • tanOf (ht i))).left := by
        refine (Category.assoc _ _ _).symm.trans (((hf.1 σ i).2 a).trans ?_)
        rw [hfj]
        exact (dualMap_epsMul φ _ _).symm
      rw [h3] at h1
      exact congrFun ((basis_map φ rfl hv hb _ (isTan_map φ rfl (isTan_tv _))).unique h1 h2) l
    subst hcc
    exact ((isComb_iff (fun i => tanOf (hv i)) g _).1 hc).trans ((isComb_iff (fun i => tanOf (hv i)) g _).1 hc').symm
  · obtain ⟨g, hc, -⟩ := hb _ (isTan_tv u)
    rw [(isComb_iff (fun i => tanOf (hv i)) g _).1 hc]
    refine Submodule.sum_mem _ fun l _ => ?_
    by_cases hl : ∃ i, e i = l
    · obtain ⟨i, rfl⟩ := hl
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, tan_ext (he i).symm⟩)
    have h0 : g l = 0 := hw _ _ fun k _ φ f hf hfj => by
      have hvk := fun i => isTan_map φ rfl (hv i)
      have huk := isTan_map φ rfl (isTan_tv u)
      obtain ⟨d, hd, -⟩ := hf.2 σ _ huk fun a => by
        rw [hfj, ← dualMap_epsMul, Category.assoc]
        exact congrArg (fun q => spMap (dualMap φ) ≫ (tv q).left) (EigenSplit.mem_eigenSub.1 hu a)
      have h1 := (comb_iff hvk _ huk).1 (comb_map φ rfl hc)
      have h2 := (comb_iff (fun i => (hf.1 σ i).1) _ huk).1 hd
      have h3 : ∑ i, d i • tanOf (hf.1 σ i).1 = ∑ l, Function.extend e d 0 l • tanOf (hvk l) :=
        Fintype.sum_of_injective e e.injective _ _
          (fun l hl => by rw [Function.extend_apply' _ _ _ hl, Pi.zero_apply, zero_smul])
          (fun i => by
            rw [e.injective.extend_apply]
            exact congrArg (d i • ·) (tan_ext (congrArg (spMap (dualMap φ) ≫ ·) (he i).symm)))
      rw [map_zero, Fintype.linearIndependent_iffₛ.1 (linInd_of_basis hvk (basis_map φ rfl hv hb)) _ _
        (h1.symm.trans (h2.trans h3)) l, Function.extend_apply' _ _ _ hl, Pi.zero_apply]
    rw [h0, zero_smul]
    exact Submodule.zero_mem _

theorem exists_basis_total (hw : FramesSeparate x c w χ) (hχ : EigenSplit.IsSplitting χ)
    (h : ∀ σ, ∃ (n : ℕ) (v : Fin n → (Sp (DualNumber S) ⟶ t.G.left)) (e : Fin (Dw.mult σ) ↪ Fin n),
      (∀ i, v (e i) = w σ i) ∧ (∀ i, IsTanAtG t x (v i)) ∧ ∀ u, IsTanAtG t x u → ∃! cf, IsCombAtG t x v cf u)
    (φ : S →+* T) {x' : Sp T ⟶ X} (hx : spMap φ ≫ x = x') :
    ∃ b : Module.Basis (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) T (TanM x' t.G), ∀ σ a, (tv (b ⟨σ, a⟩)).left = w.bc φ σ a := by
  choose n v e he hv hb using h
  have ht : ∀ σ i, IsTanAtG t x (w σ i) := fun σ i => he σ i ▸ hv σ (e σ i)
  have li : ∀ σ, LinearIndependent S fun i => tanOf (ht σ i) := fun σ => by
    obtain ⟨b, hb'⟩ := exists_basis (hv σ) (hb σ)
    convert b.linearIndependent.comp (e σ) (e σ).injective using 1
    exact funext fun i => Eq.trans (tan_ext (w := tanOf (hv σ (e σ i))) (he σ i).symm) (hb' (e σ i)).symm
  obtain ⟨b, hb'⟩ := exists_basis_sigma hχ _ (fun σ i => tanOf (ht σ i)) li
    fun σ => span_eq_eigenSub hw σ (ht σ) (e σ) (he σ) (hv σ) (hb σ)
  obtain ⟨b', hb''⟩ := exists_basis_map b φ hx
  exact ⟨b', fun σ a => by rw [hb'', hb']; rfl⟩

end Tangent

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

def embV {l : Level H} (c : Coeff l) (W : ValuationSubring ℂ) (σ : E →+* ℂ) : 𝓞 E →+* c.V W :=
  (embK c σ).codRestrict (c.V W) fun a =>
    GlobalTheory.CoeffRings.mem_of_isIntegral _ (map_isIntegral_int (embK c σ) (RingOfIntegers.isIntegral a))

theorem isSplitting_embV {l : Level H} (c : Coeff l) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits)
    (hd : ¬ p ∣ (discr E).natAbs) {S : Type} [CommRing S] (j : c.V W →+* S) :
    EigenSplit.IsSplitting fun σ : E →+* ℂ => j.comp (embV c W σ) := by
  refine EigenSplit.isSplitting_of_isDomain (fun σ τ h => ?_) (NumberField.Embeddings.card E ℂ) j ?_
  · exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
      (RingHom.ext fun a => congrArg (fun f : 𝓞 E →+* c.V W => (((f a : c.V W) : c.F) : ℂ)) h)
  · have hu := (((GlobalTheory.CoeffRings.coeff_isDedFrac E H l c).2.2.2 p W hp hW).2.1 _
      (hp.coprime_iff_not_dvd.2 hd).symm).map j
    rw [map_natCast] at hu
    rcases Int.natAbs_eq (discr E) with h | h <;> rw [h]
    · rwa [Int.cast_natCast]
    · rw [Int.cast_neg, Int.cast_natCast]
      exact hu.neg

variable {Z : Mdl Y i₀} {U : Z.X.Opens} {hU : IsAffineOpen U} {w : Vecs Dw (Y Z.i).t Γ(Z.X, U)}

variable (hU) in

theorem fn_ext_affine {f g : Γ(Z.X, U)} (h : ∀ (k : Type) [Field k] (φ : Γ(Z.X, U) →+* k),
    Set.range (spMap φ ≫ hU.fromSpec) ⊆ Z.opn → φ f = φ g) : f = g :=
  fn_ext Z fun k _ x hx ho => by
    rw [valR_eq x U hx, valR_eq x U hx]
    exact h k (valMap x U hx).hom (by
      rw [show spMap (valMap x U hx).hom ≫ hU.fromSpec = x from specMap_valMap_fromSpec hU x hx]
      exact ho)

theorem frame_at (hw : IntFrame Z hU w) {j : Z.i.c.V W →+* Γ(Z.X, U)} (hj : spMap j = hU.fromSpec ≫ Z.s)
    {k : Type} [Field k] (φ : Γ(Z.X, U) →+* k) (ho : Set.range (spMap φ ≫ hU.fromSpec) ⊆ Z.opn) :
    ∃ f : Z.i.c.F →+* k, IsFrame (Y Z.i).t f (spMap φ ≫ hU.fromSpec ≫ Z.π) (w.bc φ) ∧
      ∀ σ a, f (embK Z.i.c σ a) = φ (j (embV Z.i.c W σ a)) := by
  obtain ⟨a, ψ, hx, hf, -⟩ := hw.2 k φ ho
  rw [Category.assoc] at hf
  refine ⟨_, hf, fun σ r => ?_⟩
  have e : spMap (ψ.comp ((Z.alg a).comp (Z.i.c.V W).subtype)) = spMap (φ.comp j) := by
    rw [← spMap_comp_spMap _ ψ, ← spMap_comp_spMap _ φ, hj, ← Z.alg_s a, ← Category.assoc, hx, Category.assoc]
  exact congrArg (fun q => q.hom (embV Z.i.c W σ r)) (Spec.map_injective e)

end Model

theorem exists_basis_of_intFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ)
    (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ¬ p ∣ (discr E).natAbs →
    ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Mdl Y i₀) (U : Z.X.Opens) (hU : IsAffineOpen U)
      (w : Vecs Dw (Y Z.i).t Γ(Z.X, U)), IntFrame Z hU w → ∀ (R : Type) [CommRing R] (φ : Γ(Z.X, U) →+* R)
      (x : Sp R ⟶ Z.X), spMap φ ≫ hU.fromSpec = x →
      ∃ b : Module.Basis (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) R (TanM (x ≫ Z.π) (Y Z.i).t.G),
        ∀ σ a, (tv (b ⟨σ, a⟩)).left = w.bc φ σ a := by
  intro E _ _ _ H Dw Xo p W hp hW hd Y i₀ Z U hU w hw R _ φ x hx
  let j : Z.i.c.V W →+* Γ(Z.X, U) := (Spec.preimage (hU.fromSpec ≫ Z.s)).hom
  have hj : spMap j = hU.fromSpec ≫ Z.s := Spec.map_preimage _
  refine exists_basis_total (c := Z.i.c) (fun r s h => fn_ext_affine hU fun k _ ψ ho => ?_)
    (isSplitting_embV Z.i.c hp hW hd j) hw.1 φ (hx ▸ (Category.assoc _ _ _).symm)
  obtain ⟨f, hf, hfj⟩ := frame_at hw hj ψ ho
  exact h k ψ f hf hfj

end GlobalTheory.TotalFrame
