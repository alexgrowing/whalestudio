import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MemLineIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IncAdjYZeroMulVec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeHyperbolicLineIdealsAtPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNatMulSelfDualLatticeAtPlaceIntegral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeAtPlaceSmulIntegralMem

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Matrix ValuativeRel IsLocalRing
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.FinPlLoc GlobalTheory.IwaPlace NumberField Filter
open GlobalTheory.GoodPos
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.MiTop.Scale

variable {D : D7}

theorem nat_mul_int {x : Pl D} (m : ℕ) {b : AE D} (hb : b ∈ intAt D (· = x)) : (m : AE D) * b ∈ intAt D (· = x) :=
  ⟨Ideal.mul_mem_left _ _ hb.1, by rw [← nsmul_eq_mul, map_nsmul]; exact nsmul_mem hb.2 m⟩

theorem int_of_keeps {S : HSp D} {L : Lat S} (hL : IsSelfDualC S L) (hr : 0 < S.rank) {x : Pl D} {t : AE D}
    (h : ∀ y ∈ latV S L (· = x), t • y ∈ latV S L (· = x)) : t * idem D (· = x) ∈ intAt D (· = x) := by
  have hsd := LocSD.isSDAt_latV D S L x hL
  have he := idem_mem_intAt (D := D) (· = x)
  obtain ⟨N, hN, hup⟩ := GlobalTheory.IwaPlace.SDBound.exists_mul_mem_intAt D S x _ hsd
  obtain ⟨m, hm, hlow⟩ := hsd.2.1
  let I : AddSubgroup (AE D) := (latV S L (· = x)).map (Pi.evalAddMonoidHom (fun _ => AE D) ⟨0, hr⟩)
  obtain ⟨α, β, h1, -, h3, h4⟩ := GlobalTheory.IwaIdeals.principal_at he (mem_idAt_iff _) I (m * N) (Nat.mul_pos hm hN)
    (by rintro _ ⟨y, hy, rfl⟩; exact hsd.1 y hy _)
    (by rintro o ho _ ⟨y, hy, rfl⟩; exact ⟨o • y, GlobalTheory.IwaPlace.SDStable.smul_mem D S x _ hsd o ho y hy, rfl⟩)
    ⟨_, hlow (fun _ => (N : AE D) * idem D (· = x)) fun _ => nat_mul_int N he, by
      rw [Nat.cast_mul, mul_assoc]; rfl⟩
    (by rintro _ ⟨y, hy, rfl⟩; rw [Nat.cast_mul, mul_assoc]; exact nat_mul_int m (hup y hy _))
  obtain ⟨y, hy, e⟩ := (h4 α h1).2 (by rw [h3]; exact he)
  have := (h4 (t * α) (Ideal.mul_mem_left _ _ h1)).1 ⟨t • y, h y hy, by rw [← e]; rfl⟩
  rwa [mul_assoc, h3] at this

theorem isU_of_norm {x : Pl D} {t : AE D} (ht : t * idem D (· = x) ∈ intAt D (· = x)) (hn : IsU x (t * cA D t)) : IsU x t := by
  intro a ha
  have e := (mem_idAt_iff _ a).1 ha
  refine ⟨fun h => ?_, fun h => (hn a ha).2 ?_⟩
  · have := int_mul ht h
    rwa [mul_assoc, e] at this
  · have := int_mul (int_conj.2 ht) h
    rw [RingHom.map_mul, cA_idem] at this
    convert this using 1
    linear_combination (-(t * cA D t)) * e

theorem norm_tau {E : Type} [Field E] [StarRing E] {m n : ℕ} {G : Matrix (Fin m) (Fin m) E} {G' : Matrix (Fin n) (Fin n) E}
    {τ : Matrix (Fin m) (Fin n) E} {t lam : E} {ζ : Fin m → E} {ζ₀ : Fin n → E} (h : τᴴ * (G * τ) = t • G')
    (hτ : τ *ᵥ ζ₀ = lam • ζ) : lam * star lam * (star ζ ⬝ᵥ G *ᵥ ζ) = t * (star ζ₀ ⬝ᵥ G' *ᵥ ζ₀) := by
  have := congrArg (fun M => star ζ₀ ⬝ᵥ M *ᵥ ζ₀) h
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, hτ, smul_mulVec, dotProduct_smul, smul_eq_mul,
    mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul] at this
  rw [← this, mul_assoc]

theorem alg_norm {R : Type} [CommRing R] {A A' B B' X X' e ec l l' h k : R} (hN : l * l' * h = -(X * -X) * k) (g1 : A * A' = 1)
    (g2 : B * B' = 1) (g3 : X * X' = 1) :
    A' * -X' * e * B * l' * h * (B' * - -X' * ec * A * l * h) = -(e * ec * h * k) := by
  linear_combination (-(A * A' * B * B' * X' * X' * e * ec * h)) * hN -
    (B * B' * X * X * X' * X' * e * ec * h * k) * g1 - (X * X * X' * X' * e * ec * h * k) * g2 - ((X * X' + 1) * e * ec * h * k) * g3

theorem alg_gen {R : Type} [CommRing R] {A' B X X' e e' l li l' h k a : R} (hN : l * l' * h = -(X * -X) * k) (ee : e' * e = 1)
    (g3 : X * X' = 1) (g4 : l * li = 1) : -(A' * -X' * e * B * l' * h * (e' * a)) = k * (A' * (X * B) * li * a) := by
  linear_combination (A' * X' * B * l' * h * a) * ee - (A' * X' * B * l' * h * a) * g4 + (A' * X' * B * li * a) * hN +
    (A' * B * li * a * X * k) * g3

theorem rank_one {Z S : HSp D} {ζ₀ : Fin Z.rank → D.host.E} {LZ : Lat Z} {LS : Lat S} (hLZ : IsSelfDualC Z LZ)
    (hLS : IsSelfDualC S LS) {x : Pl D} {α : (AE D)ˣ}
    (hα : ∀ y, y ∈ latA Z LZ (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV Z LZ (· = x))
    (hμ : ∀ a ∈ idAt D (· = x), a • ratV ζ₀ ∈ latV Z LZ (· = x) ↔ a ∈ intAt D (· = x)) {s' : Fin S.rank → AE D}
    (hs' : s' ∈ latV S LS (· = x)) : ∃ w ∈ latO S Z (LS : Set _) (LZ : Set _) (· = x), ∀ y,
      (show Matrix (Fin Z.rank) (Fin S.rank) (AE D) from w) *ᵥ y = ((α : AE D) * hermAt S y s') • ratV ζ₀ := by
  have hsd := LocSD.isSDAt_latV D S LS x hLS
  have hw : ∀ y, vecMulVec ((α : AE D) • ratV ζ₀) ((fun k => cA D (s' k)) ᵥ* gA S) *ᵥ y =
      ((α : AE D) * hermAt S y s') • ratV ζ₀ := fun y => by
    rw [herm_eq, dotProduct_mulVec]
    funext i
    simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  refine ⟨vecMulVec ((α : AE D) • ratV ζ₀) ((fun k => cA D (s' k)) ᵥ* gA S),
    (LatMem.mem_latO_iff D S Z LS LZ hLS hLZ _ _).2 ⟨fun i j => ?_, fun y hy => ?_⟩, hw⟩
  · rw [vecMulVec_apply]
    refine Ideal.mul_mem_left _ _ ?_
    simp only [vecMul, dotProduct]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (id_conj (hsd.1 s' hs' k))
  · have hi := (hsd.2.2 y (hsd.1 y hy)).1 hy s' hs'
    refine (hα _).2 ((congrArg (fun t => ((α⁻¹ : (AE D)ˣ) : AE D) • t) (hw y)).symm ▸ ?_)
    rw [smul_smul, Units.inv_mul_cancel_left]
    exact (hμ _ hi.1).2 hi

theorem top_keeps {L L'' S : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) {ζ : Fin L.rank → D.host.E}
    {ζ₀ : Fin L''.rank → D.host.E} {lam : D.host.E} (hτ : τ *ᵥ ζ₀ = lam • ζ)
    {LL : Lat L} {LZ : Lat L''} {LS : Lat S} (hLL : IsSelfDualC L LL) (hLZ : IsSelfDualC L'' LZ)
    (hLS : IsSelfDualC S LS) {x : Pl D} {α : (AE D)ˣ}
    (hα : ∀ (S : HSp D) (L : Lat S) y, y ∈ latA S L (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = x))
    (hμ : ∀ a ∈ idAt D (· = x), a • ratV ζ₀ ∈ latV L'' LZ (· = x) ↔ a ∈ intAt D (· = x))
    (hk : ∀ w ∈ latO S L'' (LS : Set _) (LZ : Set _) (· = x), kap τ S w ∈ latO L S (LL : Set _) (LS : Set _) (· = x)) {e : AE D}
    (hl : (e * idem D (· = x)) • ratV ζ ∈ latV L LL (· = x)) :
    ∀ s' ∈ latV S LS (· = x), (((α⁻¹ : (AE D)ˣ) : AE D) * incA D (-D.host.xi0⁻¹) * e * cA D α * cA D (incA D lam) *
      incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ)) • s' ∈ latV S LS (· = x) := fun s' hs' => by
  have hsd := LocSD.isSDAt_latV D S LS x hLS
  generalize ht : ((α⁻¹ : (AE D)ˣ) : AE D) * incA D (-D.host.xi0⁻¹) * e * cA D α * cA D (incA D lam) *
      incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ) = t
  refine (hsd.2.2 (t • s') fun i => Ideal.mul_mem_left _ _ (hsd.1 s' hs' i)).2 fun s hs => ?_
  obtain ⟨w, hwO, hw⟩ := rank_one hLZ hLS (hα _ _) hμ hs'
  have h1 := (hα _ _ _).1 (((LatMem.mem_latO_iff D L S LL LS hLL hLS _ _).1 (hk w hwO)).2 _ hl)
  have h2 := (hsd.2.2 _ (hsd.1 _ h1)).1 h1 s hs
  have e1 := herm_smul S ((α⁻¹ : (AE D)ˣ) : AE D) 1
    ((show Matrix (Fin S.rank) (Fin L.rank) (AE D) from kap τ S w) *ᵥ (e * idem D (· = x)) • ratV ζ) s
  rw [one_smul] at e1
  rw [e1, herm_kap, hw, mulVec_smul, rat_mulVec, hτ, ratV_smul, smul_smul, herm_smul, herm_rat] at h2
  have e2 := herm_smul S t 1 s' s
  rw [one_smul] at e2
  have e3 := (mem_idAt_iff _ _).1 (LocSD.hermAt_mem_idAt (hsd.1 s' hs') s)
  rw [RingHom.map_mul, RingHom.map_mul, RingHom.map_one, herm_conj] at h2
  rw [e2, RingHom.map_one, ← ht]
  refine (iff_of_eq (congrArg (· ∈ _) ?_)).1 h2
  linear_combination (((α⁻¹ : (AE D)ˣ) : AE D) * incA D (-D.host.xi0⁻¹) * e * cA D α * cA D (incA D lam) *
    incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ)) * e3

theorem top_line {L L'' S : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) {ζ : Fin L.rank → D.host.E}
    {ζ₀ : Fin L''.rank → D.host.E} (hζ : IsLineVec L ζ) (hζ₀ : IsLineVec L'' ζ₀) {lam : D.host.E} (hlam : lam ≠ 0)
    (hτ : τ *ᵥ ζ₀ = lam • ζ) (hsim : τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram)
    {LL : Lat L} {LZ : Lat L''} {LS : Lat S} (hLL : IsSelfDualC L LL) (hLZ : IsSelfDualC L'' LZ)
    (hLS : IsSelfDualC S LS) (hr : 0 < S.rank) {x : Pl D} {α : (AE D)ˣ}
    (hα : ∀ (S : HSp D) (L : Lat S) y, y ∈ latA S L (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = x))
    (hμ : ∀ a ∈ idAt D (· = x), a • ratV ζ₀ ∈ latV L'' LZ (· = x) ↔ a ∈ intAt D (· = x))
    (hk : ∀ w ∈ latO S L'' (LS : Set _) (LZ : Set _) (· = x), kap τ S w ∈ latO L S (LL : Set _) (LS : Set _) (· = x)) :
    ∀ a ∈ idAt D (· = x), a • ratV ζ ∈ latV L LL (· = x) ↔
      (((α * (xiU D * cU α)⁻¹ * inU lam hlam)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x) := by
  obtain ⟨e, he0, hg⟩ := line_gen hζ hLL.1 x
  have hn := line_norm (μ := inU e he0) hζ hLL hg
  have h0 := line_norm (μ := 1) hζ₀ hLZ (x := x) fun a ha => by rw [inv_one, Units.val_one, one_mul]; exact hμ a ha
  rw [Units.val_one, map_one, one_mul, one_mul] at h0
  have hε := idem_mem_intAt (D := D) (· = x)
  have ee : incA D e⁻¹ * incA D e = 1 := (inU e he0).inv_mul
  have hti := int_of_keeps hLS hr (top_keeps τ hτ hLL hLZ hLS hα hμ hk (e := incA D e)
    ((hg _ (Ideal.mul_mem_left _ _ hε.1)).2 (by rwa [← mul_assoc, ee, one_mul])))
  have hc : cA D (incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ)) = incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ) := by rw [← herm_rat, herm_conj]
  have hN := congrArg (incA D) (norm_tau hsim hτ)
  rw [RingHom.map_mul, RingHom.map_mul, RingHom.map_mul, RingHom.map_neg, RingHom.map_mul, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, RingHom.map_neg,
    ← FrameLat.cA_incA lam] at hN
  have g2 : cA D (α : AE D) * cA D ((α⁻¹ : (AE D)ˣ) : AE D) = 1 := (cU α).mul_inv
  have g3 : incA D D.host.xi0 * incA D D.host.xi0⁻¹ = 1 := (xiU D).mul_inv
  have g4 : incA D lam * incA D lam⁻¹ = 1 := (inU lam hlam).mul_inv
  rw [RingHom.map_neg] at hti
  have hu := isU_of_norm hti (by
    rw [RingHom.map_mul, RingHom.map_mul, RingHom.map_mul, RingHom.map_mul, RingHom.map_mul, RingHom.map_neg, cA_cA, cA_cA, cA_xi_inv, hc,
      alg_norm hN α.mul_inv g2 g3]
    exact (hn.mul h0).neg)
  intro a ha
  rw [hg a ha, hu _ (Ideal.mul_mem_left _ _ ha), h0 _ (Ideal.mul_mem_left _ _ ha), ← int_neg, alg_gen hN ee g3 g4, mul_inv, mul_inv,
    inv_inv]
  rfl

theorem last_iff {V₀ W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (z : Fin V₀.rank → D.host.E) {M : Lat V₀} {LW : Lat W}
    (hM : IsSelfDualC V₀ M) {x : Pl D} (hLW : IsSelfDualC W LW) {α m : (AE D)ˣ} (r : Fin ρ) (hr : r.1 + 1 = ρ)
    (hα : ∀ y, y ∈ latA W LW (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV W LW (· = x))
    (hW : ∀ a ∈ idAt D (· = x), colMul d.jY r a ∈ latV W LW (· = x) ↔
      cA D ((xiU D * cU α * m : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) {a : AE D} (ha : a ∈ idAt D (· = x)) :
    d.incAdj V₀ (a • yZero V₀ ρ z) ∈ latO V₀ W (M : Set _) (LW : Set _) (· = x) ↔
      ((m : AE D) * a) • ratV z ∈ latV V₀ M (· = x) := by
  have hsd := LocSD.isSDAt_latV D V₀ M x hM
  have hmx : MxAt (· = x) (d.incAdj V₀ (a • yZero V₀ ρ z)) :=
    mxAt_mul _ (mxAt_smul _ (mxAt_mul' _ (mxAt_adj fun i j => Ideal.mul_mem_right _ _ ha)))
  rw [LatMem.mem_latO_iff D V₀ W M LW hM hLW, and_iff_right hmx,
    hsd.2.2 (((m : AE D) * a) • ratV z) fun i => Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ ha)]
  refine forall₂_congr fun y hy => ?_
  rw [incAdj_yZero_mulVec d _ hr, hα, smul_colMul, hW _
    (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (LocSD.hermAt_mem_idAt (hsd.1 y hy) _))), ← int_neg,
    ← herm_conj V₀ y, int_conj, mul_smul]
  have e1 := herm_smul V₀ 1 m y (a • ratV z)
  rw [one_smul] at e1
  rw [e1, Units.val_mul, Units.val_mul, RingHom.map_mul, RingHom.map_mul, cU_val, cA_cA, xiU, inU_val, cA_xi]
  have e2 := α.mul_inv
  have e3 : incA D D.host.xi0 * incA D D.host.xi0⁻¹ = 1 := (xiU D).mul_inv
  refine iff_of_eq (congrArg (· ∈ _) ?_)
  linear_combination (incA D D.host.xi0 * incA D D.host.xi0⁻¹ * cA D m * hermAt V₀ y (a • ratV z)) * e2 +
    (cA D m * hermAt V₀ y (a • ratV z)) * e3

theorem dual_line {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀} (hL : IsSelfDualC S L) {x : Pl D}
    (hm : MonoAt d L L₀ x) (i : Fin ρ) {b : (AE D)ˣ}
    (hX : ∀ a ∈ idAt D (· = x), colMul d.jX i a ∈ latV S L (· = x) ↔ ((b⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) :
    ∀ a ∈ idAt D (· = x), colMul d.jY i a ∈ latV S L (· = x) ↔ cA D (b : AE D) * a ∈ intAt D (· = x) := fun a ha => by
  obtain ⟨p, q, h1, -, h3, h4, h5⟩ := GlobalTheory.IwaIdeals.ideals_at_place D S S₀ ρ d L L₀ x (idem D (· = x)) (idem_mul_self _) (cA_idem _)
    (idem_mem_intAt _) (mem_idAt_iff _) (LocSD.isSDAt_latV D S L x hL) hm
  have hb : (b : AE D) * (cA D a * p i) ∈ idAt D (· = x) := Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (h1 i))
  have := (h4 i _ hb).symm.trans (hX _ hb)
  rw [Units.inv_mul_cancel_left, mul_assoc, mul_assoc, h3, mul_comm (cA D a), (mem_idAt_iff _ _).1 (id_conj ha)] at this
  rw [h5 i a ha, ← int_conj, RingHom.map_mul, cA_cA, ← this, ← int_conj, RingHom.map_mul, cA_cA]

theorem step_line {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ}
    {LV : Lat B.V} {LV₀ : Lat B.V₀} {LW : Lat J.W} {LW₀ : Lat J.W₀} {LV' : Lat B'.V} {LV₀' : Lat B'.V₀} {x : Pl D} {α m : (AE D)ˣ}
    (hα : ∀ (S : HSp D) (L : Lat S) y, y ∈ latA S L (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = x))
    (h₁ : GoodBF ψ B J LV LV₀ LW LW₀ x) (h₂ : AdaptFB ψ J B' LW LW₀ LV' LV₀' x)
    (hz : ∀ a ∈ idAt D (· = x), a • ratV (vecB B'.o B'.ζ) ∈ latV B'.V₀ LV₀' (· = x) ↔
      ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) :
    ∀ a ∈ idAt D (· = x), a • ratV (vecB B.o B.ζ) ∈ latV B.V₀ LV₀ (· = x) ↔
      (((α * (xiU D * cU α)⁻¹ * m)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x) := fun a ha => by
  have hX : ∀ a ∈ idAt D (· = x), colMul J.d.jX (Fin.last σ) a ∈ latV J.W LW (· = x) ↔
      (((α * m)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x) := fun a ha => by
    have e : ∀ t : AE D, colMul (xLast B'.d (vecB B'.o B'.ζ)) (Fin.last σ) t = B'.d.j0 *ᵥ (t • ratV (vecB B'.o B'.ζ)) := fun t => by
      funext k
      simp only [colMul, xLast, Matrix.of_apply, Fin.snoc_last, mulVec_smul, Pi.smul_apply, smul_eq_mul]
    have e0 : ∀ (M : Mx D B'.V.rank σ) i, colMul M i 0 = 0 := fun M i => funext fun k => zero_mul _
    rw [h₂.cols _ a ha, hα, smul_colMul, e, h₂.monoW, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, B'.d.pX_j0, B'.d.pY_j0,
      B'.d.p0_j0, zero_mulVec, one_mulVec, hz _ (Ideal.mul_mem_left _ _ ha), mul_inv, Units.val_mul, mul_assoc, mul_left_comm]
    simp only [Pi.zero_apply, e0, zero_mem, implies_true, true_and]
  have hY := dual_line J.d h₁.sdW h₁.monoW _ hX
  have eb : α * m = xiU D * cU α * (α * (xiU D * cU α)⁻¹ * m) := by
    rw [mul_comm α (_)⁻¹, mul_assoc _ α m, mul_inv_cancel_left]
  rw [eb] at hY
  have hb := Ideal.mul_mem_left _ (((α * (xiU D * cU α)⁻¹ * m)⁻¹ : (AE D)ˣ) : AE D) ha
  rw [← h₁.last (Nat.succ_pos σ) _ hb, last_iff J.d _ h₁.sdV₀ h₁.sdW (Fin.last σ) rfl (hα _ _) hY hb, Units.mul_inv_cancel_left]

variable {c : Comm D} {v : VCom c} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type} {o : TDat c k ι}

theorem core_line (hc : c.Is) (hs : ShapeOff v o) (hp : TopPrim v o) (hr : ∀ j, j + 2 * 0 + 2 = D.R.m → 0 < (c.X (j + 1)).rank)
    {lam : D.host.E} (hlam : lam ≠ 0) (hτ : ∀ j h, v.τ j h *ᵥ o.ζ₀ = lam • (c.bes j 0 h).ζ) {x : Pl D} (hx : x ∉ v.tP) {α : (AE D)ˣ}
    (hα : ∀ (S : HSp D) (L : Lat S) y, y ∈ latA S L (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = x)) (ρ : ℕ) :
    ∀ j (h : j + 2 * ρ + 2 = D.R.m), ∀ a ∈ idAt D (· = x),
      a • ratV (vecB (c.bes j ρ h).o (c.bes j ρ h).ζ) ∈ latV (c.bes j ρ h).V₀ (o.M j ρ h) (· = x) ↔
        ((((α * (xiU D * cU α)⁻¹) ^ (ρ + 1) * inU lam hlam)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x) := by
  induction ρ with
  | zero =>
    intro j h a ha
    obtain ⟨LL, LZ, h1, h2, h3, h4, h5⟩ := (hs.split x hx).top j h
    rw [← orth_line _ h3, zero_add, pow_one]
    exact top_line _ (c.bes j 0 h).line hs.pre.line hlam (hτ j h) (hs.pre.tau j h) h1 h2 (hc.x (j + 1) (by omega)).sd (hr j h) hα
      (fun a ha => hp.line h hx h4 ha) h5 a ha
  | succ σ ih =>
    intro j h a ha
    rw [pow_succ', mul_assoc]
    exact step_line hα ((hs.good x).bf j (σ + 1) h) ((hs.good x).fb j σ h) (ih _ (idx_step h)) a ha

end GlobalTheory.MiTop.Scale

end
