import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelPlacesNotIsConjPlaceRealDat
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BSlotD
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.NatCastKPZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

noncomputable section
namespace GlobalTheory.SeeConjGroup.CoefRead

open Classical

theorem flagVector_map_bilinear {M N P : Type} [Zero M] [Zero N] [Zero P] (φ : M → N → P) (hφ : φ 0 0 = 0) (ρ k n : ℕ)
    (e' f' : Fin ρ → M) (b' : Fin k → M) (z' : M) (e f : Fin ρ → N) (b : Fin k → N) (z : N) (q : Fin n) :
    φ (flagV ρ k n e' f' b' z' q) (flagV ρ k n e f b z q) =
      flagV ρ k n (fun a => φ (e' a) (e a)) (fun a => φ (f' a) (f a)) (fun i => φ (b' i) (b i)) (φ z' z) q := by
  unfold flagV
  split_ifs <;> simp [hφ]

theorem flagV_mem {M : Type} [Zero M] (S : Set M) (h0 : (0 : M) ∈ S) {ρ k n : ℕ} {e f : Fin ρ → M} {b : Fin k → M} {z : M}
    (he : ∀ a, e a ∈ S) (hf : ∀ a, f a ∈ S) (hb : ∀ i, b i ∈ S) (hz : z ∈ S) (q : Fin n) : flagV ρ k n e f b z q ∈ S := by
  unfold flagV
  split_ifs <;> simp_all

theorem sum_flagV {M : Type} [AddCommMonoid M] (ρ k n : ℕ) (hn : n = 2 * ρ + k + 1) (e f : Fin ρ → M) (b : Fin k → M) (z : M) :
    ∑ q : Fin n, flagV ρ k n e f b z q = (∑ a, e a) + (∑ i, b i) + z + ∑ a, f a := by
  subst hn
  rw [← Fin.sum_congr' _ (show ρ + (k + (1 + ρ)) = 2 * ρ + k + 1 by ring)]
  rw [Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_one]
  have h1 : ∀ a : Fin ρ, flagV ρ k (2 * ρ + k + 1) e f b z (Fin.cast (by ring) (Fin.castAdd (k + (1 + ρ)) a)) = e a := by
    intro a
    unfold flagV
    simp
  have h2 : ∀ i : Fin k, flagV ρ k (2 * ρ + k + 1) e f b z
      (Fin.cast (by ring) (Fin.natAdd ρ (Fin.castAdd (1 + ρ) i))) = b i := by
    intro i
    unfold flagV
    simp
  have h3 : flagV ρ k (2 * ρ + k + 1) e f b z
      (Fin.cast (by ring) (Fin.natAdd ρ (Fin.natAdd k (Fin.castAdd ρ (0 : Fin 1))))) = z := by
    unfold flagV
    simp
  have h4 : ∀ a : Fin ρ, flagV ρ k (2 * ρ + k + 1) e f b z
      (Fin.cast (by ring) (Fin.natAdd ρ (Fin.natAdd k (Fin.natAdd 1 a)))) = f (Fin.rev a) := by
    intro a
    unfold flagV
    have := a.2
    simp only [Fin.val_cast, Fin.val_natAdd]
    rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
    congr 1
    ext
    simp [Fin.val_rev]
    omega
  simp only [h1, h2, h3, h4]
  rw [show (∑ a : Fin ρ, f (Fin.rev a)) = ∑ a, f a from Equiv.sum_comp Fin.revPerm f]
  abel

theorem memLf (D : D7) (v : Fin (Yc D 0).rank → EAf D) : v ∈ (II D).Lf ↔
    v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (E := D.host.E) ((II D).L : Submodule (𝓞 D.host.E) (Fin (Yc D 0).rank → D.host.E)) :=
  Set.ext_iff.1 (Formalism.IndefR.Eqv.lamAf_eq_hatL (V := Yc D 0) (II D).L) v

theorem rank_val (D : D7) : (Yc D 0).rank = 2 * D.R.rS + D.R.k + 1 := by
  rw [show (Yc D 0).rank = D.R.r from Formalism.L2.SG.InstExistsPf.rank_eq D]
  obtain ⟨j, hj⟩ := D.R.m_even; have := D.R.two_le_m; simp only [Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS]; omega

open Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.BunEx.Unip in
theorem hA_neg_left' (I : AutInst) (a b : VA I) : hA I (-a) b = - hA I a b := by
  rw [show -a = (-1 : I.E ⊗[I.F] Af I.F) • a by simp, hA_smul_left]
  simp

open Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.BunEx.Unip in
theorem resS_zero_of {D : D7} (PP : Pl D.host.E) {x c : EAf D} (hx : x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (e : x = c * x) (h0 : resS D.host.F PP ⟨c, hc⟩ = 0) :
    resS D.host.F PP ⟨x, hx⟩ = 0 := by
  have : (⟨x, hx⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨c, hc⟩ * ⟨x, hx⟩ := Subtype.ext e
  rw [this, map_mul, h0, zero_mul]

open Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.BunEx.Unip in
theorem ew_int {D : D7} {g : ℕ} {e0 f0 : Fin D.R.rS → VA (II D)} {z0 : VA (II D)} {bw bwd : Fin D.R.k → VA (II D)}
    {ew : (II D).E ⊗[(II D).F] Af (II D).F} (hF : Formalism.L2.SG.Pf.BunEx.Unip.FH (II D) g e0 f0 z0 bw bwd ew) (i : Fin D.R.k) :
    ew ∈ IntAf (II D).F (II D).E := by
  obtain ⟨t, ht, e⟩ := hF.dual i i
  simp only [if_true] at e
  have h1 : hA (II D) (bwd i) (bw i) ∈ IntAf (II D).F (II D).E := hA_int (II D) (hF.mem.2.2 i).2 (hF.mem.2.2 i).1
  have h2 : ((g : ℕ) : (II D).E ⊗[(II D).F] Af (II D).F) * t ∈ IntAf (II D).F (II D).E :=
    Subring.mul_mem _ (natCast_mem _ g) ht
  have : ew = hA (II D) (bwd i) (bw i) - (g : (II D).E ⊗[(II D).F] Af (II D).F) * t := by rw [← e]; ring
  rw [this]
  exact Subring.sub_mem _ h1 h2

open Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.BunEx.Unip in
theorem second {D : D7} {g : ℕ} {e0 f0 : Fin D.R.rS → VA (II D)} {z0 : VA (II D)} {bw bwd : Fin D.R.k → VA (II D)}
    {ew : (II D).E ⊗[(II D).F] Af (II D).F} (hF : Formalism.L2.SG.Pf.BunEx.Unip.FH (II D) g e0 f0 z0 bw bwd ew) {β : GL (Fin (Yc D 0).rank) (EAf D)}
    {PP : Pl D.host.E} {w : Bool} (hL : LocAt g e0 f0 z0 bw bwd ew β PP w) (u : VA (II D)) (i : Fin D.R.k)
    (h1 : hA (II D) ((if w then bw else bwd) i) u ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    resS D.host.F PP ⟨_, h1⟩ = 0 := by
  have hew := ew_int hF i
  cases w
  · have e : hA (II D) (bwd i) u = ew * hA (II D) (bwd i) u := by
      conv_lhs => rw [hF.bwd_w i]
      rw [hA_smul_left, sigA_sigA]
    exact resS_zero_of PP h1 hew e (by simpa using hL.2.1 hew)
  · have hs := sigA_mem (II D) hew
    have e : hA (II D) (bw i) u = sigA (II D) ew * hA (II D) (bw i) u := by
      conv_lhs => rw [hF.bw_w i]
      rw [hA_smul_left]
    exact resS_zero_of PP h1 hs e (by simpa using hL.2.2.1 hs)

open Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.BunEx.Unip in
theorem Rc_flag {D : D7} (e0 f0 : Fin D.R.rS → VA (II D)) (z0 : VA (II D)) (bw bwd : Fin D.R.k → VA (II D)) (w : Bool)
    (u : VA (II D)) :
    Rc (II D) e0 f0 z0 bw bwd u =
      (∑ q : Fin (Yc D 0).rank, hA (II D) (flagV D.R.rS D.R.k (Yc D 0).rank f0 e0 (dualOrRevBasis w bw bwd) (-z0) q) u •
        flagV D.R.rS D.R.k (Yc D 0).rank e0 f0 (basisOrRevDual w bw bwd) z0 q) +
      ∑ i, hA (II D) ((if w then bw else bwd) i) u • (if w then bwd else bw) i := by
  have hq := fun q => flagVector_map_bilinear (fun x y : VA (II D) => hA (II D) x u • y) (by simp) D.R.rS D.R.k (Yc D 0).rank
    f0 e0 (dualOrRevBasis w bw bwd) (-z0) e0 f0 (basisOrRevDual w bw bwd) z0 q
  simp only [hq]
  rw [sum_flagV _ _ _ (rank_val D)]
  unfold Rc
  cases w
  · simp only [basisOrRevDual, dualOrRevBasis, Bool.false_eq_true, if_false, hA_neg_left', neg_smul]
    rw [show (∑ x : Fin D.R.k, hA (II D) (bw x.rev) u • bwd x.rev) = ∑ x, hA (II D) (bw x) u • bwd x from
      Equiv.sum_comp Fin.revPerm (fun i => hA (II D) (bw i) u • bwd i)]
    abel
  · simp only [basisOrRevDual, dualOrRevBasis, if_true, hA_neg_left', neg_smul]
    abel

theorem key_gen {A : Type} [CommRing A] (S : Subring A) {n ι κ : Type} [Fintype n] [DecidableEq n] [Fintype ι] [Fintype κ]
    (M : Matrix n n A) (u : n → A) (c : ι → A) (G : ι → n → A) (d : κ → A) (o : κ → n → A) (gg : A) (z : n → A)
    (hu : u = (∑ q, c q • G q) + (∑ i, d i • o i) + gg • z) (p : n) (hup : (M *ᵥ u) p ∈ S)
    (hc : ∀ q, c q ∈ S) (hG : ∀ q, (M *ᵥ G q) p ∈ S) (hd : ∀ i, d i ∈ S) (ho : ∀ i, (M *ᵥ o i) p ∈ S)
    (hg : gg ∈ S) (hz : (M *ᵥ z) p ∈ S) :
    (⟨_, hup⟩ : S) = (∑ q, ⟨_, hc q⟩ * ⟨_, hG q⟩) + (∑ i, ⟨_, hd i⟩ * ⟨_, ho i⟩) + ⟨_, hg⟩ * ⟨_, hz⟩ := by
  apply Subtype.ext
  subst hu
  simp [Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.sum_apply]

theorem read_gen {A K : Type} [CommRing A] [CommRing K] (S : Subring A) (φ : S →+* K) {n κ : Type} [Fintype n]
    [DecidableEq n] [Fintype κ] (M : Matrix n n A) (u : n → A) (c : n → A) (G : n → n → A) (d : κ → A) (o : κ → n → A)
    (gg : A) (z : n → A) (hu : u = (∑ q, c q • G q) + (∑ i, d i • o i) + gg • z) (p : n) (hup : (M *ᵥ u) p ∈ S)
    (hc : ∀ q, c q ∈ S) (hG : ∀ q, (M *ᵥ G q) p ∈ S) (hd : ∀ i, d i ∈ S) (ho : ∀ i, (M *ᵥ o i) p ∈ S)
    (hg : gg ∈ S) (hz : (M *ᵥ z) p ∈ S) (hδ : ∀ q, φ ⟨_, hG q⟩ = if p = q then 1 else 0)
    (hd0 : ∀ i, φ ⟨_, hd i⟩ = 0) (hg0 : φ ⟨_, hg⟩ = 0) :
    φ ⟨_, hc p⟩ = φ ⟨_, hup⟩ := by
  rw [key_gen S M u c G d o gg z hu p hup hc hG hd ho hg hz, map_add, map_add, map_sum, map_sum, map_mul, hg0, zero_mul,
    add_zero]
  simp only [map_mul, hd0, zero_mul, Finset.sum_const_zero, add_zero, hδ, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

theorem resS_natCast {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (PP : Pl E) (g : ℕ)
    (hg : (g : 𝓞 E) ∈ PP.asIdeal) : resS F PP (g : Formalism.L2.Herm.intAf F E) = 0 := by
  rw [map_natCast, ← map_natCast (Ideal.Quotient.mk PP.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
  exact hg

theorem redV_of {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (PP : Pl E) (v : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) (j : Fin n)
    (h : ((β⁻¹).val *ᵥ v) j ∈ Formalism.L2.Herm.intAf F E) : redV β PP v j = resS F PP ⟨_, h⟩ := dif_pos h

set_option maxHeartbeats 1000000 in
open Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.BunEx.Unip in
theorem coef_read : ∀ {D : D7} (g : ℕ) (e0 f0 : Fin D.R.rS → VA (II D)) (z0 : VA (II D)) (bw bwd : Fin D.R.k → VA (II D)) (ew : EAf D), Formalism.L2.SG.Pf.BunEx.Unip.FH (II D) g e0 f0 z0 bw bwd ew → ∀ (β : GL (Fin (Yc D 0).rank) (EAf D)) (PP : Pl D.host.E) (w : Bool), IsFrame β (II D).L → LocAt g e0 f0 z0 bw bwd ew β PP w → ∀ u ∈ (II D).Lf, (∀ p (h1 : hA (II D) (flagV D.R.rS D.R.k (Yc D 0).rank f0 e0 (dualOrRevBasis w bw bwd) (-z0) p) u ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), resS D.host.F PP ⟨_, h1⟩ = redV β PP u p) ∧ (∀ i (h1 : hA (II D) ((if w then bw else bwd) i) u ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), resS D.host.F PP ⟨_, h1⟩ = 0) := by
  intro D g e0 f0 z0 bw bwd ew hF β PP w hβ hL u hu
  refine ⟨fun p h1 => ?_, fun i h1 => second hF hL u i h1⟩
  have hint : ∀ v ∈ (II D).Lf, ∀ j, ((β⁻¹).val *ᵥ v) j ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun v hv => (hβ v).1 ((memLf D v).1 hv)
  have hexp := Formalism.L2.SG.Pf.BunEx.Unip.exp hF u hu
  obtain ⟨z, hz, hzm⟩ := Formalism.L2.SG.Pf.BunEx.Unip.mL_dvd (dvd_refl g) _ hexp
  have hu' := sub_eq_iff_eq_add'.1 hzm
  rw [Rc_flag e0 f0 z0 bw bwd w u] at hu'
  have hred := hL.2.2.2
  have hsD : ∀ i, dualOrRevBasis w bw bwd i ∈ (II D).Lf := by
    intro i; cases w
    · exact (hF.mem.2.2 _).1
    · exact (hF.mem.2.2 _).2
  have hDv : ∀ q, flagV D.R.rS D.R.k (Yc D 0).rank f0 e0 (dualOrRevBasis w bw bwd) (-z0) q ∈ (II D).Lf :=
    fun q => flagV_mem ((II D).Lf : Set (VA (II D))) (zero_mem _) (fun a => (hF.mem.1 a).2) (fun a => (hF.mem.1 a).1)
      hsD (neg_mem hF.mem.2.1) q
  have ho : ∀ i, (if w then bwd else bw) i ∈ (II D).Lf := by
    intro i; cases w
    · exact (hF.mem.2.2 _).1
    · exact (hF.mem.2.2 _).2
  have hoD : ∀ i, (if w then bw else bwd) i ∈ (II D).Lf := by
    intro i; cases w
    · exact (hF.mem.2.2 _).2
    · exact (hF.mem.2.2 _).1
  have hC : ∀ q, hA (II D) (flagV D.R.rS D.R.k (Yc D 0).rank f0 e0 (dualOrRevBasis w bw bwd) (-z0) q) u ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := fun q => hA_int (II D) (hDv q) hu
  have hCo : ∀ i, hA (II D) ((if w then bw else bwd) i) u ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun i => hA_int (II D) (hoD i) hu
  have hGi : ∀ q, ((β⁻¹).val *ᵥ
      flagV D.R.rS D.R.k (Yc D 0).rank e0 f0 (basisOrRevDual w bw bwd) z0 q) p ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun q => (hred p q).fst
  have hoi : ∀ i, ((β⁻¹).val *ᵥ (if w then bwd else bw) i) p ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := fun i => hint _ (ho i) p
  have hzi := hint z hz p
  have hui := hint u hu p
  have hgI : ((g : ℕ) : (II D).E ⊗[(II D).F] Af (II D).F) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := natCast_mem _ g
  have key := key_gen (Formalism.L2.Herm.intAf D.host.F D.host.E) (β⁻¹).val u _ _ _ _ _ z hu' p hui hC hGi hCo hoi hgI hzi
  have hgc : (⟨_, hgI⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = (g : Formalism.L2.Herm.intAf D.host.F D.host.E) := Subtype.ext (by push_cast; rfl)
  rw [hgc] at key
  have hg0 : resS D.host.F PP ⟨_, hgI⟩ = 0 := by
    rw [hgc]; exact resS_natCast PP g hL.1
  have hδ : ∀ q, resS D.host.F PP ⟨_, hGi q⟩ = if p = q then 1 else 0 := fun q => (hred p q).snd
  have hfin := read_gen (Formalism.L2.Herm.intAf D.host.F D.host.E) (resS D.host.F PP) (β⁻¹).val u _ _ _ _ _ z hu' p hui hC hGi
    hCo hoi hgI hzi hδ (fun i => second hF hL u i (hCo i)) hg0
  have hR := redV_of β PP u p hui
  rw [hR]
  exact hfin

end GlobalTheory.SeeConjGroup.CoefRead
