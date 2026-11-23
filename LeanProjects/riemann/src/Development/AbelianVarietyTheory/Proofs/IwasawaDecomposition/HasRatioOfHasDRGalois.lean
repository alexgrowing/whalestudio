import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasPRatio
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineDomainFrameHasDRStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootsOfUnityAndPValuationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitTorsOfGenericLevelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentBasisOfSplitTorsionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFrameResidueStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PresentationTangentCombinationStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)

namespace GlobalTheory.HTLine.Ratio

attribute [local instance] Over.cartesianMonoidalCategory

section Fam

def pf {R : Type} [Mul R] {m n : ℕ} (A : Fin m → R) (B : Fin n → R) : Fin (m * n) → R :=
  fun q => A (finProdFinEquiv.symm q).1 * B (finProdFinEquiv.symm q).2

theorem pf_pair {R : Type} [Mul R] {m n : ℕ} (A : Fin m → R) (B : Fin n → R) (i : Fin m) (j : Fin n) :
    pf A B (finProdFinEquiv (i, j)) = A i * B j := by
  simp [pf]

theorem exists_norm_eq {C : Type} [NormedField C] {m : ℕ} [NeZero m] (x : Fin m → C) : ∃ i, ‖x‖ = ‖x i‖ := by
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖x i‖) ⟨0, Finset.mem_univ _⟩
  exact ⟨i, le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => hi j (Finset.mem_univ _))
    (norm_le_pi_norm x i)⟩

theorem norm_pf {C : Type} [NormedField C] {m n : ℕ} (x : Fin m → C) (y : Fin n → C) : ‖pf x y‖ = ‖x‖ * ‖y‖ := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (by positivity)).2 fun q => ?_) ?_
  · rw [pf, norm_mul]
    exact mul_le_mul (norm_le_pi_norm x _) (norm_le_pi_norm y _) (norm_nonneg _) (norm_nonneg _)
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · have : ‖x‖ = 0 := by rw [norm_eq_zero]; exact Subsingleton.elim _ _
      rw [this, zero_mul]; exact norm_nonneg _
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : ‖y‖ = 0 := by rw [norm_eq_zero]; exact Subsingleton.elim _ _
      rw [this, mul_zero]; exact norm_nonneg _
    haveI : NeZero m := ⟨hm.ne'⟩
    haveI : NeZero n := ⟨hn.ne'⟩
    obtain ⟨i, hi⟩ := exists_norm_eq x
    obtain ⟨j, hj⟩ := exists_norm_eq y
    rw [hi, hj, ← norm_mul, ← pf_pair]
    exact norm_le_pi_norm _ _

theorem radical_pf {R : Type} [CommRing R] {m n : ℕ} {A : Fin m → R} {B : Fin n → R} {r : R}
    (hA : r ∈ (Ideal.span (Set.range A)).radical) (hB : r ∈ (Ideal.span (Set.range B)).radical) :
    r ∈ (Ideal.span (Set.range (pf A B))).radical := by
  have e : Ideal.span (Set.range (pf A B)) = Ideal.span (Set.range A) * Ideal.span (Set.range B) := by
    rw [Ideal.span_mul_span']
    congr 1
    ext z
    constructor
    · rintro ⟨q, rfl⟩
      exact Set.mul_mem_mul ⟨_, rfl⟩ ⟨_, rfl⟩
    · rintro ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
      exact ⟨finProdFinEquiv (i, j), pf_pair A B i j⟩
  rw [e, Ideal.radical_mul]
  exact ⟨hA, hB⟩

theorem norm_pos_of_radical {R C : Type} [CommRing R] [NormedField C] [CharZero C] (χ : R →+* C) {p : ℕ} (hp : p ≠ 0)
    {m : ℕ} {A : Fin m → R} (h : (p : R) ∈ (Ideal.span (Set.range A)).radical) : 0 < ‖fun j => χ (A j)‖ := by
  refine lt_of_le_of_ne (norm_nonneg _) fun e => ?_
  have h0 : ∀ j, χ (A j) = 0 := fun j => congrFun (norm_eq_zero.1 e.symm) j
  obtain ⟨n, hn⟩ := h
  have : (p : R) ^ n ∈ RingHom.ker χ := Ideal.span_le.2 (by rintro _ ⟨j, rfl⟩; exact h0 j) hn
  rw [RingHom.mem_ker, map_pow, map_natCast] at this
  exact pow_ne_zero n (Nat.cast_ne_zero.2 hp : (p : C) ≠ 0) this

theorem comp_pf {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) {m n : ℕ} (A : Fin m → R) (B : Fin n → R) :
    (fun q => ψ (pf A B q)) = pf (fun j => ψ (A j)) (fun j => ψ (B j)) := by
  funext q
  simp [pf]

theorem comp_single {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) (a : R) :
    (fun j => ψ ((![a] : Fin 1 → R) j)) = ![ψ a] := by
  funext j
  fin_cases j
  rfl

theorem norm_single {C : Type} [NormedField C] (c : C) : ‖(![c] : Fin 1 → C)‖ = ‖c‖ := by
  have : (![c] : Fin 1 → C) = fun _ => c := by
    funext j
    fin_cases j
    rfl
  rw [this, pi_norm_const]

theorem log_ratio {g₁ b₁ a₁ g₀ b₀ a₀ s c : ℝ} (hb₁ : 0 < b₁) (ha₁ : 0 < a₁) (hb₀ : 0 < b₀) (ha₀ : 0 < a₀) (hs : 0 < s)
    (h₁ : g₁ * b₁ = a₁) (h₀ : g₀ * b₀ = a₀) (hc : Real.log s = -c) :
    (Real.log g₁ - c) - (Real.log g₀ - 0) = Real.log (s * a₁ * b₀) - Real.log (b₁ * a₀) := by
  have n₁ : g₁ ≠ 0 := fun e => ha₁.ne' (by rw [← h₁, e, zero_mul])
  have n₀ : g₀ ≠ 0 := fun e => ha₀.ne' (by rw [← h₀, e, zero_mul])
  have e₁ : Real.log g₁ + Real.log b₁ = Real.log a₁ := by rw [← h₁, Real.log_mul n₁ hb₁.ne']
  have e₀ : Real.log g₀ + Real.log b₀ = Real.log a₀ := by rw [← h₀, Real.log_mul n₀ hb₀.ne']
  rw [Real.log_mul (mul_pos hs ha₁).ne' hb₀.ne', Real.log_mul hs.ne' ha₁.ne', Real.log_mul hb₁.ne' ha₀.ne']
  linarith

end Fam

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

open GlobalTheory.ShFam.Pad.Pull

theorem gen_eq {Z : Mdl Y i₀} {U : Z.X.Opens} (hU : IsAffineOpen U) (y : Z.Pt) {χ : Γ(Z.X, U) →+* ↥(intO ↥y.C.S)}
    (hχ : spMap χ ≫ hU.fromSpec = y.z) : spMap ((intO ↥y.C.S).subtype.comp χ) ≫ hU.fromSpec = y.gen := by
  rw [Mdl.Pt.gen, ← hχ, ← GlobalTheory.ModelRelProbe.spMap_comp, Category.assoc]

theorem diff_frame (hB : HTBoundSt) (hp : p.Prime) (Z : Mdl Y i₀) (hty : ∀ τ n, n ≤ Dw.mult τ → n ∈ Z.ty τ)
    {U : Z.X.Opens} (hU : IsAffineOpen U) {w : Vecs Dw (Y Z.i).t Γ(Z.X, U)} (hw : IntFrame Z hU w) (y : Z.Pt)
    (a : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* ↥y.C.S) (hφ : spMap φ ≫ Z.chart a = y.gen)
    (χ : Γ(Z.X, U) →+* ↥(intO ↥y.C.S)) (hχ : spMap χ ≫ hU.fromSpec = y.z)
    {st : ((E →+* ℂ) × ℕ) ⊕ ℕ} {x : Letter Dw} (hx : letterOf Dw st = some x) :
    lnStep (Y Z.i).t (y.gen ≫ Z.π) ((Z.fr a).bc φ) p true st -
        lnStep (Y Z.i).t (y.gen ≫ Z.π) ((Z.fr a).bc φ) p false st =
      lnStep (Y Z.i).t (y.gen ≫ Z.π) (w.bc ((intO ↥y.C.S).subtype.comp χ)) p true st -
        lnStep (Y Z.i).t (y.gen ≫ Z.π) (w.bc ((intO ↥y.C.S).subtype.comp χ)) p false st := by
  have hgen := gen_eq hU y hχ
  obtain ⟨ψ, hψ⟩ : ∃ ψ, ψ = (intO ↥y.C.S).subtype.comp χ := ⟨_, rfl⟩
  rw [← hψ] at hgen ⊢
  obtain ⟨a₁, φ₁, h₁, hF, hS⟩ := hw.2 _ ψ (hgen ▸ range_opn Z hφ)
  rw [hgen] at h₁ hF hS
  have := mono_spMap_subtype (Z.i.c.V W)
  have hf : φ₁.comp (Z.alg a₁) = φ.comp (Z.alg a) := by
    refine congrArg CommRingCat.Hom.hom (Spec.map_injective (a₁ := CommRingCat.ofHom _) (a₂ := CommRingCat.ofHom _) ?_)
    rw [← cancel_mono (spMap (Z.i.c.V W).subtype)]
    exact (affineOpenChart_comp_structure_eq_spMap Z h₁).symm.trans (affineOpenChart_comp_structure_eq_spMap Z hφ)
  rw [hf] at hF
  have hu := chart_frame Z hφ
  have hT : ∀ τ, Tri (Y Z.i).t (y.gen ≫ Z.π) ((Z.fr a).bc φ τ) (w.bc ψ τ) := fun τ =>
    Tri.trans (fun i => (chart_frame Z hφ).1 τ i |>.1) (fun i => (chart_frame Z h₁).1 τ i |>.1)
      (chart_tri Z hty hφ h₁ τ) (tri_of_sameFlag hty hS τ)
  obtain ⟨cf, -, hc⟩ := hT x.1 x.2
  have hxe : y.gen ≫ Z.π = spMap (intO ↥y.C.S).subtype ≫ y.z ≫ Z.π := Category.assoc _ _ _
  rw [hxe] at hu hF hT hc ⊢
  have key := fun b => lnStep_tri (p := p) hB hp y.C b (y.z ≫ Z.π) (fun q hq => ext_unique Z.i _ _ hq) hu hF hT hx hc
  rw [key true, key false]
  ring

theorem exists_ratio (hB : HTBoundSt) (hp : p.Prime) (Z : Mdl Y i₀) (hty : ∀ τ n, n ≤ Dw.mult τ → n ∈ Z.ty τ)
    {U : Z.X.Opens} (hU : IsAffineOpen U) {w : Vecs Dw (Y Z.i).t Γ(Z.X, U)} (hw : IntFrame Z hU w)
    {st : ((E →+* ℂ) × ℕ) ⊕ ℕ} {x : Letter Dw} (hx : letterOf Dw st = some x) {n : ℕ}
    (fam : Fin n → (Sp (DualNumber Γ(Z.X, U)) ⟶ (Y Z.i).t.G.left)) (i : Fin n) (c : ℝ) (a : Γ(Z.X, U))
    (ha : (p : Γ(Z.X, U)) ∈ (Ideal.span {a}).radical)
    (hc : ∀ (C : SCF p) (φ : Γ(Z.X, U) →+* ↥(intO ↥C.S)), Real.log ‖((φ a : ↥(intO ↥C.S)) : ↥C.S)‖ = -c)
    (hst : ∀ (y : Z.Pt) (b : Bool) (ψ : Γ(Z.X, U) →+* ↥y.C.S),
      lnStep (Y Z.i).t (y.gen ≫ Z.π) (w.bc ψ) p b st =
        Real.log (grNorm (Y Z.i).t (y.gen ≫ Z.π) (lat (Y Z.i).t p (y.gen ≫ Z.π) b)
          (fun j => spMap (dualMap ψ) ≫ fam j) i) - (if b then c else 0))
    (hg : ∀ b : Bool, ∃ (a₁ a₂ : ℕ) (A : Fin a₁ → Γ(Z.X, U)) (B : Fin a₂ → Γ(Z.X, U)),
      (p : Γ(Z.X, U)) ∈ (Ideal.span (Set.range A)).radical ∧ (p : Γ(Z.X, U)) ∈ (Ideal.span (Set.range B)).radical ∧
      ∀ (C : SCF p) (φ : Γ(Z.X, U) →+* ↥(intO ↥C.S)),
        grNorm (Y Z.i).t (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ hU.fromSpec ≫ Z.π)
          (lat (Y Z.i).t p (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ hU.fromSpec ≫ Z.π) b)
          (fun j => spMap (dualMap ((intO ↥C.S).subtype.comp φ)) ≫ fam j) i *
            ‖fun j => ((φ (B j) : ↥(intO ↥C.S)) : ↥C.S)‖ = ‖fun j => ((φ (A j) : ↥(intO ↥C.S)) : ↥C.S)‖) :
    ∃ (m m' : ℕ) (A : Fin m → Γ(Z.X, U)) (B : Fin m' → Γ(Z.X, U)), RatioAt Z st U A B := by
  obtain ⟨m₁, m₁', A₁, B₁, hA₁, hB₁, h₁⟩ := hg true
  obtain ⟨m₀, m₀', A₀, B₀, hA₀, hB₀, h₀⟩ := hg false
  have ha' : (p : Γ(Z.X, U)) ∈ (Ideal.span (Set.range ![a])).radical := by simpa using ha
  refine ⟨_, _, pf (pf ![a] A₁) B₀, pf B₁ A₀, radical_pf (radical_pf ha' hA₁) hB₀, radical_pf hB₁ hA₀, ?_⟩
  intro y a' φ hφ hU'
  obtain ⟨χ, hχ⟩ := exists_fromSpec hU y.z hU'
  rw [diff_frame hB hp Z hty hU hw y a' φ hφ χ hχ hx, hst, hst]
  have hgen := gen_eq hU y hχ
  have hxe : spMap (intO ↥y.C.S).subtype ≫ spMap χ ≫ hU.fromSpec ≫ Z.π = y.gen ≫ Z.π := by
    rw [Mdl.Pt.gen, ← hχ]
    simp only [Category.assoc]
  have e₁ := h₁ y.C χ
  have e₀ := h₀ y.C χ
  rw [hxe] at e₁ e₀
  have hval : ∀ s, valF y.gen U s = (intO ↥y.C.S).subtype.comp χ s := fun s => by rw [← hgen, valF_fromSpec]
  simp only [hval, comp_pf, comp_single, norm_pf, norm_single]
  have p₁ := norm_pos_of_radical ((intO ↥y.C.S).subtype.comp χ) hp.ne_zero hB₁
  have q₁ := norm_pos_of_radical ((intO ↥y.C.S).subtype.comp χ) hp.ne_zero hA₁
  have p₀ := norm_pos_of_radical ((intO ↥y.C.S).subtype.comp χ) hp.ne_zero hB₀
  have q₀ := norm_pos_of_radical ((intO ↥y.C.S).subtype.comp χ) hp.ne_zero hA₀
  have ps := norm_pos_of_radical ((intO ↥y.C.S).subtype.comp χ) hp.ne_zero ha'
  rw [comp_single, norm_single] at ps
  simpa using log_ratio p₁ q₁ p₀ q₀ ps e₁ e₀ (hc y.C χ)

theorem lnStep_inl {X : Scheme.{0}} (t : SAB H X) {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
    (x : Sp C ⟶ X) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber C) ⟶ t.G.left)) (p : ℕ) (b : Bool)
    (τ : E →+* ℂ) {k : ℕ} (h : k < Dw.mult τ) :
    lnStep t x u p b (.inl (τ, k)) = Real.log (grNorm t x (lat t p x b) (u τ) ⟨k, h⟩) -
      (if b ∧ τ (H.rt : E) = H.rt0 then vDiff E p * Real.log p else 0) := by
  simp only [lnStep, dif_pos h]

theorem lnStep_inr {X : Scheme.{0}} (t : SAB H X) {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
    (x : Sp C ⟶ X) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber C) ⟶ t.G.left)) (p : ℕ) (b : Bool)
    {k : ℕ} (h : k < (letters Dw).length) :
    lnStep t x u p b (.inr k) = Real.log (grNorm t x (lat t p x b)
      (fun i => u ((letters Dw).get i).1 ((letters Dw).get i).2) ⟨k, h⟩) := by
  simp only [lnStep, dif_pos h]

end Main

theorem hasRatio : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → IsGalois ℚ E → ∀ (Z : Mdl Y i₀), HasDR Z → p ∣ Z.i.l.A → ∀ st (x : Letter Dw), letterOf Dw st = some x → HasRatio Z st := by
  intro hB E _ _ _ H Dw Xo p W Y i₀ hp hW hGal Z hZ hdvd st x hx z
  obtain ⟨U, hU, hdom, w, g, e, β, y, hz, hic, hβ, hw, he, hy⟩ := GlobalTheory.T.exists_affine_domain_frame_hasDR E H Dw Xo p W Y i₀ hp hW Z hZ z
  have hty : ∀ τ n, n ≤ Dw.mult τ → n ∈ Z.ty τ := fun τ n hn => by
    rw [hZ.1 τ]
    exact Finset.mem_range.2 (Nat.lt_succ_of_le hn)
  haveI : CharZero ↥(Z.i.c.V W) := inferInstance
  have hcz : CharZero Γ(Z.X, U) := ⟨fun m n h => Nat.cast_injective (R := ↥(Z.i.c.V W)) (hβ (by simpa using h))⟩
  obtain ⟨hroots, hdiff⟩ := GlobalTheory.T.roots_of_unity_and_p_valuation E H Z.i.l Z.i.c p W hp hW
  obtain ⟨ζ, hζ⟩ := hroots p hdvd
  obtain ⟨a₀, ha₀, hv⟩ := hdiff hGal
  have hsp := @GlobalTheory.T.splitTors_of_generic_level E _ _ _ H Dw Z.i.l (Xo Z.i.l) Z.i.c _ _ (Z.i.c.V W).subtype (Y Z.i) Γ(Z.X, U) _ hdom
    (hU.fromSpec ≫ Z.π) y hy p hdvd
  have hsep := GlobalTheory.ShFam.Pad.Pull.isSeparated_base (Y := Y) Z.i
  haveI := GlobalTheory.ProjBlowup.isDiscreteValuationRing_coeff Z.i.c hp.ne_zero hW
  haveI : IsProper (Y Z.i).s := projProper _ _ _ (Y Z.i).proj
  have hln : IsLocallyNoetherian (Y Z.i).X := LocallyOfFiniteType.isLocallyNoetherian (Y Z.i).s
  have hpres := @GlobalTheory.T.tangent_basis_of_split_torsion hB E _ _ _ H (Y Z.i).X (Y Z.i).t hln hsep p hp Γ(Z.X, U) _ hdom hic hcz (hU.fromSpec ≫ Z.π)
    ⟨β ζ, hζ.map_of_injective hβ⟩ hsp g e he
  have hind := GlobalTheory.T.integral_frame_residue E H Dw Xo p W Y i₀ hp hW Z U hU w hw
  have htan : ∀ τ i, IsTanAtG (Y Z.i).t (hU.fromSpec ≫ Z.π) (w τ i) := fun τ i => by
    obtain ⟨n, v, f, h₁, h₂, -⟩ := hw.1 τ
    exact h₁ i ▸ h₂ (f i)
  have hgn : ∀ {n : ℕ} (fam : Fin n → (Sp (DualNumber Γ(Z.X, U)) ⟶ (Y Z.i).t.G.left)),
      (∀ j, IsTanAtG (Y Z.i).t (hU.fromSpec ≫ Z.π) (fam j)) →
      (∀ (k : Type) [Field k] (ψ : Γ(Z.X, U) →+* k), (p : k) ≠ 0 →
        GlobalTheory.ShFam.Pad.Pull.Ind (Y Z.i).t (spMap ψ ≫ hU.fromSpec ≫ Z.π) (fun j => spMap (dualMap ψ) ≫ fam j)) →
      ∀ (i : Fin n) (b : Bool), ∃ (a₁ a₂ : ℕ) (A : Fin a₁ → Γ(Z.X, U)) (B : Fin a₂ → Γ(Z.X, U)),
      (p : Γ(Z.X, U)) ∈ (Ideal.span (Set.range A)).radical ∧ (p : Γ(Z.X, U)) ∈ (Ideal.span (Set.range B)).radical ∧
      ∀ (C : SCF p) (φ : Γ(Z.X, U) →+* ↥(intO ↥C.S)),
        grNorm (Y Z.i).t (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ hU.fromSpec ≫ Z.π)
          (lat (Y Z.i).t p (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ hU.fromSpec ≫ Z.π) b)
          (fun j => spMap (dualMap ((intO ↥C.S).subtype.comp φ)) ≫ fam j) i *
            ‖fun j => ((φ (B j) : ↥(intO ↥C.S)) : ↥C.S)‖ = ‖fun j => ((φ (A j) : ↥(intO ↥C.S)) : ↥C.S)‖ :=
    fun {n} fam h₁ h₂ i b => by
      obtain ⟨M, h, hP⟩ := hpres b
      exact GlobalTheory.T.presentation_tangent_combination E H _ (Y Z.i).t _ (hU.fromSpec ≫ Z.π) p b g M e h hp he hP n fam h₁ h₂ i
  have hone : (p : Γ(Z.X, U)) ∈ (Ideal.span {(1 : Γ(Z.X, U))}).radical := by
    rw [Ideal.span_singleton_one, Ideal.radical_top]
    exact Submodule.mem_top
  have hlog1 : ∀ (C : SCF p) (φ : Γ(Z.X, U) →+* ↥(intO ↥C.S)),
      Real.log ‖((φ 1 : ↥(intO ↥C.S)) : ↥C.S)‖ = -0 := fun C φ => by simp
  rcases st with ⟨τ, k⟩ | k
  · have hk : k < Dw.mult τ := by
      by_contra h
      simp [letterOf, h] at hx
    have hG := hgn (w τ) (htan τ) (fun k' _ ψ h => (hind k' ψ h).1 τ) ⟨k, hk⟩
    by_cases hr : τ (H.rt : E) = H.rt0
    · obtain ⟨m, m', A, B, h⟩ := exists_ratio hB hp Z hty hU hw hx (w τ) ⟨k, hk⟩ (vDiff E p * Real.log p) (β a₀)
        (by
          obtain ⟨n, hn⟩ := ha₀
          refine ⟨n, Ideal.mem_span_singleton.2 ?_⟩
          have := map_dvd β (Ideal.mem_span_singleton.1 hn)
          simpa using this)
        (fun C φ => hv C (φ.comp β))
        (fun y b ψ => by
          rw [lnStep_inl _ _ _ _ _ _ hk]
          cases b <;> simp [hr] <;> rfl) hG
      exact ⟨U, m, m', A, B, hz, hU, h⟩
    · obtain ⟨m, m', A, B, h⟩ := exists_ratio hB hp Z hty hU hw hx (w τ) ⟨k, hk⟩ 0 1 hone hlog1
        (fun y b ψ => by
          rw [lnStep_inl _ _ _ _ _ _ hk]
          cases b <;> simp [hr] <;> rfl) hG
      exact ⟨U, m, m', A, B, hz, hU, h⟩
  · have hk : k < (letters Dw).length := by
      by_contra h
      simp [letterOf, List.getElem?_eq_none (not_lt.1 h)] at hx
    obtain ⟨m, m', A, B, h⟩ := exists_ratio hB hp Z hty hU hw hx
      (fun i : Fin (letters Dw).length => w ((letters Dw).get i).1 ((letters Dw).get i).2) ⟨k, hk⟩ 0 1 hone hlog1
      (fun y b ψ => by
        rw [lnStep_inr _ _ _ _ _ hk]
        cases b <;> simp <;> rfl)
      (hgn _ (fun j => htan _ _) (fun k' _ ψ h => (hind k' ψ h).2) ⟨k, hk⟩)
    exact ⟨U, m, m', A, B, hz, hU, h⟩

end GlobalTheory.HTLine.Ratio
