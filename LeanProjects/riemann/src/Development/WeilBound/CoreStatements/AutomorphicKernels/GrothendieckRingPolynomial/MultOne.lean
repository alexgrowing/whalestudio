import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.ProdList
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CanonicalSegmentsReverseOrderedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCanonicalSegmentOrderStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReverseOrderedProductPermEquivStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CanonicalProductEquivMultiplicityOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPosStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityOfEquivStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLengthStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JhMultMulLeOfSteps
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos

set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Groth

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace GrothendieckSingleMultiplication

section Ring

theorem mulR_sg_left (a : IrrGL k) (b : GrothGL k) :
    mulR (sg a) b = b.sum fun y n => n • cl0 (prod₂ (IrrGL.rep a) (IrrGL.rep y)) := by
  unfold mulR sg
  rw [Finsupp.sum_single_index]
  · simp only [one_mul]
  · simp

theorem mulR_sg_zero (a : IrrGL k) : mulR (sg a) 0 = 0 := by
  rw [mulR_sg_left, Finsupp.sum_zero_index]

theorem mulR_sg_add (a : IrrGL k) (b c : GrothGL k) : mulR (sg a) (b + c) = mulR (sg a) b + mulR (sg a) c := by
  simp only [mulR_sg_left]
  exact Finsupp.sum_add_index' (fun _ => zero_smul _ _) fun _ _ _ => add_smul _ _ _

theorem mulR_sg_zsmul (a : IrrGL k) (n : ℤ) (b : GrothGL k) : mulR (sg a) (n • b) = n • mulR (sg a) b :=
  (AddMonoidHom.mk' (mulR (sg a)) (mulR_sg_add a)).map_zsmul n b

theorem sum_single_one_smul (T : IrrGL k → GrothGL k) (b : IrrGL k) :
    (Finsupp.single b (1 : ℤ)).sum (fun y n => n • T y) = T b := by
  rw [Finsupp.sum_single_index] <;> simp

theorem mulR_sg_sg (a b : IrrGL k) : mulR (sg a) (sg b) = cl0 (prod₂ (IrrGL.rep a) (IrrGL.rep b)) := by
  rw [mulR_sg_left]
  exact sum_single_one_smul (fun y => cl0 (prod₂ (IrrGL.rep a) (IrrGL.rep y))) b

theorem mulR_sg_left_comm (ha : Assoc k) (hc : Comm k) (a b : IrrGL k) (c : GrothGL k) :
    mulR (sg a) (mulR (sg b) c) = mulR (sg b) (mulR (sg a) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [mulR_sg_zero]
  | add f g hf hg => rw [mulR_sg_add, mulR_sg_add, hf, hg, mulR_sg_add, mulR_sg_add]
  | single z n =>
    have hs : Finsupp.single z n = n • sg z := by simp [sg]
    rw [hs, mulR_sg_zsmul, mulR_sg_zsmul, mulR_sg_zsmul, mulR_sg_zsmul, ← ha a b z, mulR_sg_sg a b,
      hc a b, ← mulR_sg_sg b a, ha b a z]

theorem foldr_perm (ha : Assoc k) (hc : Comm k) {l₁ l₂ : List (IrrGL k)} (p : l₁.Perm l₂) (u : GrothGL k) :
    l₁.foldr (fun y a => mulR (sg y) a) u = l₂.foldr (fun y a => mulR (sg y) a) u := by
  induction p with
  | nil => rfl
  | cons x _ ih => simp only [List.foldr_cons, ih]
  | swap x y l => simp only [List.foldr_cons]; exact mulR_sg_left_comm ha hc y x _
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

end Ring

theorem jordan_holder_mult_eq_of_class (y : IrrGL k) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GL (Fin y.1) k) V) (π' : Representation ℂ (GL (Fin y.1) k) W)
    (hπ : HasFiniteLength π) (hπ' : HasFiniteLength π') (h : cl0 π = cl0 π') :
    jhMult (IrrGL.rep y) π = jhMult (IrrGL.rep y) π' := by
  have e1 : cl0 π = clsGL π hπ := by unfold cl0; rw [dif_pos hπ]
  have e2 : cl0 π' = clsGL π' hπ' := by unfold cl0; rw [dif_pos hπ']
  have h2 := congrArg (fun a : GrothGL k => a ⟨y.1, y.2⟩) (e1.symm.trans (h.trans e2))
  simp only [clsGL_apply, cls_apply] at h2
  have h3 : (jhMult (IrrGL.rep y) π).toNat = (jhMult (IrrGL.rep y) π').toNat := by exact_mod_cast h2
  rw [← ENat.natCast_toNat (jhMult_ne_top y.2.rep.irr hπ), ← ENat.natCast_toNat (jhMult_ne_top y.2.rep.irr hπ'), h3]

theorem jhMult_mul_jm_le {g N : ℕ} (z : Fin g → IrrGL k) (hz : ∑ b, (z b).1 = N) {V W : Type}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V)
    (τ : Representation ℂ (GL (Fin N) k) W) (hπ : IsSmooth π) :
    jhMult τ π * jm z hz τ ≤ jm z hz π := by
  have hadd : ∀ S T : Subrepresentation π, T ≤ S →
      jm z hz T.toRepresentation + jm z hz (subQuot S T) ≤ jm z hz S.toRepresentation := by
    intro S T h
    let ι : T.toRepresentation.IntertwiningMap S.toRepresentation := ⟨Submodule.inclusion h, fun _ => rfl⟩
    let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
    have hS : IsSmooth S.toRepresentation :=
      (IsSubquotient.of_injective (⟨S.toSubmodule.subtype, fun _ => rfl⟩ :
        S.toRepresentation.IntertwiningMap π) Subtype.val_injective).isSmooth hπ
    refine GlobalTheory.CompanionTheory.CsStages.jhMult_add_le (jacMap _ ι) (jacMap _ p)
      (GlobalTheory.JacquetExact.jacMap_injective _ hS ι (Submodule.inclusion_injective h))
      (GlobalTheory.JacquetExact.jacMap_surjective _ p (Submodule.Quotient.mk_surjective _)) fun u => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    have : p (ι v) = 0 := (Submodule.Quotient.mk_eq_zero _).2 v.2
    show Submodule.Quotient.mk (p (ι v)) = 0
    rw [this]
    rfl
  have h := GlobalTheory.CompanionTheory.CsStages.jhMult_mul_le_of_steps τ π (fun S => jm z hz S.toRepresentation) (jm z hz τ)
    (fun S T h => le_trans le_self_add (hadd S T h))
    (fun S T h ⟨φ⟩ => by
      have := hadd S T h
      rwa [GlobalTheory.T.jacquet_multiplicity_of_equiv z hz _ _ ⟨φ⟩] at this)
  rwa [GlobalTheory.T.jacquet_multiplicity_of_equiv z hz _ _ ⟨topEquiv π⟩] at h

theorem ofFn_perm {α : Type*} {h : ℕ} (x : Fin h → α) (σ : Equiv.Perm (Fin h)) :
    (List.ofFn (x ∘ σ)).Perm (List.ofFn x) := by
  exact Equiv.Perm.ofFn_comp_perm σ x

theorem jhMult_le_one_of_equiv (y : IrrGL k) {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin y.1) k) V} {g : ℕ} {z : Fin g → IrrGL k} {hz : ∑ b, (z b).1 = y.1}
    (hsoc : IsSocle (IrrGL.rep y) π) (e : π.Equiv (prodIrr z hz)) (hjm : jm z hz (prodIrr z hz) ≤ 1) :
    jhMult (IrrGL.rep y) π ≤ 1 := by
  have hA := PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  obtain ⟨hirr, f, hf, -⟩ := hsoc
  have hnt := nontrivial_of_irreducible hirr
  obtain ⟨v, hv⟩ := exists_ne (0 : y.2.rep.V)
  have hpos : 1 ≤ jm z hz (IrrGL.rep y) :=
    GlobalTheory.T.jacquet_multiplicity_pos hA z hz (IrrGL.rep y) y.2.rep.smooth (e.toIntertwiningMap.comp f)
      ⟨v, fun h0 => hv (hf (e.injective (by simpa using h0)))⟩
  have hle := jhMult_mul_jm_le z hz (prodIrr z hz) (IrrGL.rep y) (isSmooth_prodIrr z hz)
  rw [jhMult_congr_right _ e]
  exact (le_mul_of_one_le_right' hpos).trans (hle.trans hjm)

theorem jhMult_rev_le_one (c : Cls k) (_𝔪 : Multiset (Segment k)) {h : ℕ} (x : Fin h → IrrGL k) (y : IrrGL k)
    (Δ : Fin h → Segment k) (hΔo : ∀ i j, i < j → ¬ (Δ i).Precedes (Δ j)) (hΔL : ∀ i, IsLSeg (Δ i) (x i).rep)
    (hdr : ∑ a, (x (Fin.rev a)).1 = y.1) (hsoc : IsSocle (IrrGL.rep y) (prodIrr (x ∘ Fin.rev) hdr)) :
    jhMult (IrrGL.rep y) (prodIrr (x ∘ Fin.rev) hdr) ≤ 1 := by
  have hA := PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have hΓ : IsRevOrdered (Δ ∘ Fin.rev) := fun i j hij => hΔo (Fin.rev j) (Fin.rev i) (Fin.rev_lt_rev.2 hij)
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_canonical_segment_order (Δ ∘ Fin.rev)
  have hσr := GlobalTheory.T.canonical_segments_reverse_ordered _ hσ
  have hdrs : ∑ a, ((x ∘ Fin.rev) (σ a)).1 = y.1 := by
    rw [← hdr]; exact Equiv.sum_comp σ (fun a => ((x ∘ Fin.rev) a).1)
  obtain ⟨e1⟩ := GlobalTheory.T.reverse_ordered_product_perm_equiv hA c.com (Δ ∘ Fin.rev) σ (x ∘ Fin.rev) hdr hdrs hΓ hσr (fun i => hΔL (Fin.rev i))
  obtain ⟨g, z, hz, ⟨e2⟩, hjm⟩ :=
    GlobalTheory.T.canonical_product_equiv_multiplicity_one hA c.jac c.unl ((Δ ∘ Fin.rev) ∘ σ) ((x ∘ Fin.rev) ∘ σ) hdrs hσ (fun i => hΔL (Fin.rev (σ i)))
  have e : (prodIrr (x ∘ Fin.rev) hdr).Equiv (prodIrr z hz) := e1.trans e2
  exact jhMult_le_one_of_equiv y hsoc e hjm

end GrothendieckSingleMultiplication

open GrothendieckSingleMultiplication in
variable (k) in
theorem multOne (c : Cls k) (_hm : MulCls k) (ha : Assoc k) (hc : Comm k) (_h1 : One k) (hl : ProdList k) :
    MultOne k := by
  intro 𝔪 h x y hd hx hy
  have hA := PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  obtain ⟨Δ, ⟨hΔm, hΔo⟩, hΔL⟩ := hx
  have hdr : ∑ a, (x (Fin.rev a)).1 = y.1 := by
    rw [← hd]; exact Equiv.sum_comp Fin.revPerm (fun a => (x a).1)
  have hsoc : IsSocle (IrrGL.rep y) (prodIrr (x ∘ Fin.rev) hdr) :=
    by have hs := c.soc; unfold LSocleGL at hs; exact hs 𝔪 h y.1 x hdr ⟨Δ, ⟨hΔm, hΔo⟩, hΔL⟩ (IrrGL.rep y) hy
  have hcl : cl0 (prodIrr x hd) = cl0 (prodIrr (x ∘ Fin.rev) hdr) := by
    rw [hl h y.1 x hd, hl h y.1 (x ∘ Fin.rev) hdr]
    exact foldr_perm ha hc (ofFn_perm x Fin.revPerm).symm _
  rw [jordan_holder_mult_eq_of_class y _ _ (GlobalTheory.T.product_irreducible_finite_length hA x hd) (GlobalTheory.T.product_irreducible_finite_length hA (x ∘ Fin.rev) hdr) hcl]
  exact le_antisymm (jhMult_rev_le_one c 𝔪 x y Δ hΔo hΔL hdr hsoc)
    (Order.one_le_iff_ne_zero.2 (jhMult_ne_zero_iff.2 hsoc.isSubquotient))

end PositivityTheory.Groth
