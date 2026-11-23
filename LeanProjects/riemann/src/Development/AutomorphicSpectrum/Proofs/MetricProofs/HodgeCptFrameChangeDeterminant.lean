import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameCoeffsRegularInChart
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsJoinBlocksStatement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DetT

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Graph

theorem det_mul_expand {R : Type} [CommRing R] {r n : ℕ} (B : Matrix (Fin r) (Fin n) R)
    (C : Matrix (Fin n) (Fin r) R) :
    (B * C).det = ∑ f : Fin r → Fin n, (∏ i, B i (f i)) * (C.submatrix f id).det :=
  _root_.UpperTheory.Reformulated.B.Ygb2.main B C

section Point

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem exists_unitAt_of_sum (hg : IsCptGen ξ) (p : Cpt ξ) {ι : Type} (s : Finset ι) (f : ι → Ω)
    (hf : ∀ i ∈ s, f i ∈ regAt ξ p) (h1 : ∑ i ∈ s, f i = 1) : ∃ i ∈ s, unitAt ξ p (f i) := by
  classical
  have hf' : ∀ i, ∃ g : X.presheaf.stalk p.1, i ∈ s → genMap ξ p g = f i := fun i => by
    by_cases hi : i ∈ s
    · obtain ⟨g, hg⟩ := hf i hi
      exact ⟨g, fun _ => hg⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose g hgf using hf'
  have hs : ∑ i ∈ s, g i = 1 := hg.inj p (by
    rw [map_sum, map_one, Finset.sum_congr rfl (fun i hi => hgf i hi), h1])
  by_contra hcon
  push_neg at hcon
  have hnu : ∀ i ∈ s, g i ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk p.1) := by
    intro i hi
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    refine hcon i hi ?_
    have e := hgf i hi
    have hu' : IsUnit (f i) := e ▸ hu.map (genMap ξ p)
    refine ⟨hu'.ne_zero, hf i hi, ⟨((hu.unit⁻¹ : (X.presheaf.stalk p.1)ˣ) : X.presheaf.stalk p.1), ?_⟩⟩
    have h2 : genMap ξ p ((hu.unit⁻¹ : (X.presheaf.stalk p.1)ˣ) : X.presheaf.stalk p.1) * f i = 1 := by
      rw [← e, ← map_mul, ← map_one (genMap ξ p)]
      congr 1
      exact hu.val_inv_mul
    exact eq_inv_of_mul_eq_one_left h2
  have h1m : (1 : X.presheaf.stalk p.1) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk p.1) :=
    hs ▸ Ideal.sum_mem _ hnu
  exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal _).ne_top h1m

theorem det_mem_subring {R : Subring Ω} {r : ℕ} (M : Matrix (Fin r) (Fin r) Ω) (h : ∀ i j, M i j ∈ R) :
    M.det ∈ R := by
  rw [Matrix.det_apply']
  exact sum_mem fun σ _ => mul_mem (intCast_mem R _) (prod_mem fun i _ => h _ _)

variable {E : Type} [AddCommGroup E] [Module Ω E]

theorem exists_inChart_minors (hg : IsCptGen ξ) {κ : Type} (x : κ → Ω) (L : Lat ξ E) {m n r : ℕ}
    (V : Submodule Ω E) (φ : Fin n → Module.Dual Ω E) (b : Fin r → E) (hv : L.IsVB r V)
    (hT : IsTwistGen ξ x L m φ) (hs : Submodule.span Ω (Set.range b) = V) (p : Cpt ξ) (c : κ)
    (hc : InChart ξ x c p) :
    ∃ J : Fin r → Fin n, InChart ξ
      (fun J : Fin r → Fin n => ((Matrix.of fun j l => φ j (b l) : Matrix (Fin n) (Fin r) Ω).submatrix J id).det)
      J p := by
  classical
  obtain ⟨U, hpU, β, hβs, hfr⟩ := hv p (Set.mem_univ _)
  have hfrp := hfr p (Set.mem_univ _) hpU
  obtain ⟨B, hBr, hCr, hBC⟩ := GlobalTheory.CompanionTheory.Ar.FlagBun.twist_left_inverse X Ω ξ E κ x L m n r φ hT p c hc β hfrp
  set C : Matrix (Fin n) (Fin r) Ω := Matrix.of (fun j a => φ j (β a) / x c ^ m) with hC
  set A : Matrix (Fin n) (Fin r) Ω := Matrix.of fun j l => φ j (b l) with hA
  have hxm : x c ^ m ≠ 0 := pow_ne_zero _ hc.1

  have hβ : ∀ a, ∃ t : Fin r → Ω, ∑ l, t l • b l = β a := fun a => by
    have : β a ∈ Submodule.span Ω (Set.range b) := by
      rw [hs, ← hβs]
      exact Submodule.subset_span ⟨a, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun Ω).1 this
  choose T hTb using hβ
  set T' : Matrix (Fin r) (Fin r) Ω := Matrix.of T with hT'
  have hAC : ∀ J : Fin r → Fin n, (A.submatrix J id).det * T'.det = (x c ^ m) ^ r * (C.submatrix J id).det := by
    intro J
    have e : A.submatrix J id * T'ᵀ = (x c ^ m) • C.submatrix J id := by
      ext i a
      simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, id, Matrix.smul_apply,
        smul_eq_mul, hA, hC, hT', Matrix.of_apply]
      rw [mul_div_cancel₀ _ hxm, ← hTb a, map_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [map_smul, smul_eq_mul, mul_comm]
    have := congrArg Matrix.det e
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Fintype.card_fin] at this
  have hdreg : ∀ J : Fin r → Fin n, (C.submatrix J id).det ∈ regAt ξ p := fun J =>
    det_mem_subring _ fun i a => hCr _ _
  have hsum := det_mul_expand B C
  rw [hBC, Matrix.det_one] at hsum
  obtain ⟨J, -, hu⟩ := exists_unitAt_of_sum hg p Finset.univ
    (fun f : Fin r → Fin n => (∏ i, B i (f i)) * (C.submatrix f id).det)
    (fun f _ => mul_mem (prod_mem fun i _ => hBr _ _) (hdreg f)) hsum.symm
  have hd0 : (C.submatrix J id).det ≠ 0 := right_ne_zero_of_mul hu.1
  have hPr : (∏ i, B i (J i)) ∈ regAt ξ p := prod_mem fun i _ => hBr _ _
  have hdinv : (C.submatrix J id).det⁻¹ ∈ regAt ξ p := by
    have e : (C.submatrix J id).det⁻¹ =
        (∏ i, B i (J i)) * ((∏ i, B i (J i)) * (C.submatrix J id).det)⁻¹ := by
      have := left_ne_zero_of_mul hu.1
      field_simp
    rw [e]
    exact mul_mem hPr hu.2.2
  have h0 : (A.submatrix J id).det * T'.det ≠ 0 := by
    rw [hAC J]
    exact mul_ne_zero (pow_ne_zero _ hxm) hd0
  have hz0 : (A.submatrix J id).det ≠ 0 := left_ne_zero_of_mul h0
  have ht0 : T'.det ≠ 0 := right_ne_zero_of_mul h0
  refine ⟨J, hz0, fun J' => ?_⟩
  have e : (A.submatrix J' id).det / (A.submatrix J id).det =
      (C.submatrix J' id).det * (C.submatrix J id).det⁻¹ := by
    have e1 := hAC J
    have e2 := hAC J'
    have hw : (x c ^ m) ^ r ≠ 0 := pow_ne_zero _ hxm
    rw [← eq_div_iff ht0] at e1 e2
    rw [e1, e2]
    field_simp
  show (A.submatrix J' id).det / (A.submatrix J id).det ∈ regAt ξ p
  rw [e]
  exact mul_mem (hdreg J') hdinv

theorem coordTie_seg_equiv {K₀ K' K : Type} [Fintype K₀] [Fintype K'] [Fintype K] {J₀ : K₀ → Type} {J' : K' → Type}
    {J : K → Type} [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J' k)] (e : K₀ ⊕ K' ≃ K)
    (F : ∀ a, Sum.elim J₀ J' a ≃ J (e a)) (x₀ : (Σ k, J₀ k) → Ω) (w : (Σ k, J' k) → Ω) (y : (Σ k, J k) → Ω)
    (h₁ : ∀ k i, y ⟨e (.inl k), F (.inl k) i⟩ = x₀ ⟨k, i⟩)
    (h₂ : ∀ k i, y ⟨e (.inr k), F (.inr k) i⟩ = w ⟨k, i⟩)
    (h : CoordTie ℤ ξ (seg x₀)) (hw : ∀ (k : K') (p : Cpt ξ), ∃ i, InChart ξ (fun i' : J' k => w ⟨k, i'⟩) i p) :
    CoordTie ℤ ξ (seg y) := by
  have h2 := GlobalTheory.T.coords_join_blocks X Ω ξ K₀ J₀ x₀ K' J' w h hw
  have h3 := GlobalTheory.CompanionTheory.Ar.FlagBun.coordTie_comp_equiv h2 (Equiv.piCongr e F).symm
  convert h3 using 1
  funext c'
  obtain ⟨c, rfl⟩ := (Equiv.piCongr e F).surjective c'
  simp only [Function.comp, Equiv.symm_apply_apply]
  show ∏ k, y ⟨k, Equiv.piCongr e F c k⟩ = _
  rw [← Equiv.prod_comp e, Fintype.prod_sum_type]
  simp only [Equiv.piCongr_apply_apply, h₁, h₂]

end Point

section Blocks

variable {Ψ : Type} [Fintype Ψ] {p q : ℕ}

abbrev FullStep (Ψ : Type) (p q : ℕ) : Type := {t : StepIx Ψ p q // (t.2 : ℕ) + 1 = rk Ψ p q t.1}

theorem blkF_ne_full (K₀ : Type) (t : FullStep Ψ p q) (r : Ψ × Fin (p + q)) :
    blkF Ψ p q K₀ r ≠ some (.inr t.1) := by
  classical
  obtain ⟨⟨s, j⟩, ht⟩ := t
  obtain ⟨τ, i⟩ := r
  unfold blkF
  split_ifs with hp
  · intro h
    have h' : stepOf Ψ p q (τ, i) = ⟨s, j⟩ := by simpa using h
    unfold stepOf at h'
    obtain ⟨hp1, hp2⟩ := hp
    split_ifs at h' with hi
    · cases h'
      exact hp1 ht
    · cases h'
      have := i.2
      apply hp2
      simp only [Sum.elim_inr] at ht hi ⊢
      omega
  · simp

theorem exists_blkF_of_not_full (K₀ : Type) (t : StepIx Ψ p q) (ht : (t.2 : ℕ) + 1 ≠ rk Ψ p q t.1) :
    ∃ r, blkF Ψ p q K₀ r = some (.inr t) := by
  classical
  obtain ⟨s, j⟩ := t
  have hj := j.2
  rcases s with τ | τ
  · simp only [Sum.elim_inl] at ht hj
    refine ⟨(τ, ⟨j, by omega⟩), ?_⟩
    have hP : IsProperStep (p + q) p (⟨j, by omega⟩ : Fin (p + q)) := ⟨ht, by simp only; omega⟩
    unfold blkF
    rw [if_pos hP]
    unfold stepOf
    simp only [dif_pos hj]
  · simp only [Sum.elim_inr] at ht hj
    refine ⟨(τ, ⟨p + j, by omega⟩), ?_⟩
    have hP : IsProperStep (p + q) p (⟨p + j, by omega⟩ : Fin (p + q)) :=
      ⟨by simp only; omega, by simp only; omega⟩
    unfold blkF
    rw [if_pos hP]
    unfold stepOf
    have hn : ¬ (p + (j : ℕ) < p) := by omega
    simp only [dif_neg hn]
    congr 2
    exact congrArg (fun z => (⟨.inr τ, z⟩ : StepIx Ψ p q)) (Fin.ext (by simp))

variable (Ψ p q) in

def baseFun (K₀ : Type) : K₀ ⊕ FullStep Ψ p q → NonPluckerBlocks (blkF Ψ p q K₀)
  | .inl k => ⟨.inl k, fun r => by
      classical
      unfold blkF
      split_ifs <;> simp⟩
  | .inr t => ⟨.inr t.1, fun r => blkF_ne_full K₀ t r⟩

theorem baseFun_bijective (K₀ : Type) : Function.Bijective (baseFun Ψ p q K₀) := by
  constructor
  · rintro (k | t) (k' | t') h
    · simpa [baseFun] using h
    · simp [baseFun] at h
    · simp [baseFun] at h
    · have : t.1 = t'.1 := by simpa [baseFun] using h
      exact congrArg _ (Subtype.ext this)
  · rintro ⟨k | t, hk⟩
    · exact ⟨.inl k, rfl⟩
    · by_cases ht : (t.2 : ℕ) + 1 = rk Ψ p q t.1
      · exact ⟨.inr ⟨t, ht⟩, rfl⟩
      · obtain ⟨r, hr⟩ := exists_blkF_of_not_full K₀ t ht
        exact absurd hr (hk r)

variable (Ψ p q) in

def baseEquiv (K₀ : Type) : K₀ ⊕ FullStep Ψ p q ≃ NonPluckerBlocks (blkF Ψ p q K₀) :=
  Equiv.ofBijective _ (baseFun_bijective K₀)

variable {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}

abbrev fullIx (n : Ψ ⊕ Ψ → ℕ) (t : FullStep Ψ p q) : Type := Fin ((t.1.2 : ℕ) + 1) → Fin (n t.1.1)

def fullMinor (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) : (Σ t : FullStep Ψ p q, fullIx n t) → Ω :=
  fun r => ((A r.1.1.1).submatrix r.2 (Fin.castLE r.1.1.2.2)).det

variable {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)]

def baseIxEquiv (n : Ψ ⊕ Ψ → ℕ) : ∀ a : K₀ ⊕ FullStep Ψ p q, Sum.elim J₀ (fullIx n) a ≃
    baseIdx (idx (p := p) (q := q) J₀ n) (blkF Ψ p q K₀) (baseEquiv Ψ p q K₀ a)
  | .inl _ => Equiv.refl _
  | .inr _ => Equiv.refl _

theorem coordTie_seg_xb {X : Scheme.{0}} (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (x₀ : (Σ k, J₀ k) → Ω)
    (h : CoordTie ℤ ξ (seg x₀))
    (hw : ∀ (t : FullStep Ψ p q) (P : Cpt ξ), ∃ J, InChart ξ
      (fun J : fullIx n t => ((A t.1.1).submatrix J (Fin.castLE t.1.2.2)).det) J P) :
    CoordTie ℤ ξ (seg (xb (p := p) (q := q) A x₀)) := by
  classical
  haveI : Fintype (FullStep Ψ p q) := Fintype.ofFinite _
  exact coordTie_seg_equiv (baseEquiv Ψ p q K₀) (baseIxEquiv n) x₀ (fullMinor A) _
    (fun _ _ => rfl) (fun _ _ => rfl) h hw

end Blocks

theorem exists_inChart_minors_cast {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {E : Type} [AddCommGroup E] [Module Ω E] (hg : IsCptGen ξ) {κ : Type} (x : κ → Ω) (L : Lat ξ E) {m n r r' : ℕ}
    (hle : r' ≤ r) (hr : r' = r)
    (V : Submodule Ω E) (φ : Fin n → Module.Dual Ω E) (b : Fin r → E) (hv : L.IsVB r V)
    (hT : IsTwistGen ξ x L m φ) (hs : Submodule.span Ω (Set.range b) = V) (p : Cpt ξ) (c : κ)
    (hc : InChart ξ x c p) :
    ∃ J : Fin r' → Fin n, InChart ξ
      (fun J : Fin r' → Fin n =>
        ((Matrix.of fun j l => φ j (b l) : Matrix (Fin n) (Fin r) Ω).submatrix J (Fin.castLE hle)).det) J p := by
  subst hr
  exact exists_inChart_minors hg x L V φ b hv hT hs p c hc

theorem coordTie_base : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → CoordTie ℤ 𝔐.ξ (seg (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO n m φ hF
  obtain ⟨hvb, hbas, htw, -⟩ := hF
  refine coordTie_seg_xb 𝔐.ξ _ x₀ 𝔐.tie fun t P => ?_
  obtain ⟨c', hc'⟩ := 𝔐.tie.cover P
  exact exists_inChart_minors_cast 𝔐.tie.gen _ (LL 𝔐 t.1.1) t.1.2.2 t.2 (VV 𝔐 t.1.1) (φ t.1.1)
    (cc 𝔐 bW bO t.1.1) (hvb _) (htw _) (hbas _).2 P c' hc'

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Graph
