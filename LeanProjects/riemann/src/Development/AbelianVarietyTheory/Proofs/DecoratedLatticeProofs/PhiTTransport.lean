import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CongAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedInvMulLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValSubLtOfHasRes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicMatrixCongruenceBadPrimeIffCompletion

noncomputable section

namespace GlobalTheory.Transport.LevelDatum

section Gen

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]

theorem mem_localization_iff {n : ℕ} {g : GL (Fin n) (AfE F E)} {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N)
    (hg : Formalism.L2.Herm.Carries g (stdLat E n) N) (P : HeightOneSpectrum (𝓞 E)) (z : Sp E n) :
    z ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N ↔ ∀ i, Valued.v (adAt F P (Col2.pullV g z i)) ≤ 1 := by
  classical
  have e : N = Formalism.UG.CS.globLat g (stdLat E n) := by
    have h1 := Formalism.UG.P.global_lattice_one_holds F E (Fin n) N (Module.Finite.iff_fg.2 hN.fg) hN.span_eq_top
    ext v
    conv_lhs => rw [← h1]
    have e1 : ∀ (x : GL (Fin n) (AfE F E)) (Λ : Submodule (𝓞 E) (Fin n → E)) (v : Fin n → E),
        v ∈ Formalism.UG.CS.globLat x Λ ↔ ((x⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
          (fun i => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (v i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ :=
      fun _ _ _ => Iff.rfl
    rw [e1, e1, inv_one, Units.val_one, Matrix.one_mulVec]
    exact hg _
  rw [e]
  constructor
  · intro hz i
    exact PtExist.valued_pullV_le g hz i
  · intro h
    have h' : ∀ i, IntAtA (F := F) P (Formalism.L2.Col.pullV g z i) := fun i => (AdT.AdelicValuationDictionary.intAtA_iff P _).2 (h i)
    choose s hs hsz using h'
    have hT : (∏ i, s i) ∉ P.asIdeal := by
      intro hm
      obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff (hp := P.isPrime)).1 hm
      exact hs i hi
    refine (mem_locP P _ z).2 ⟨∏ i, s i, hT, ?_⟩
    rw [mem_globLat]
    intro i
    rw [pullV_osmul, ← Finset.prod_erase_mul Finset.univ s (Finset.mem_univ i), map_mul, map_mul, mul_assoc]
    exact mul_mem (iA_mem _) (hsz i)

variable {hc : Formalism.BasicNotions.CMData F E}

theorem hasRes_f {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q}
    (hg : IsPtOf hc g p) (P : ST) {z : Sp E n} (hz : z ∈ p.deco.1.at P.1) {i : Fin n} (hi : i.1 + 1 = n) :
    HasRes P.1 (adAt F P.1 (Col2.pullV g z i)) (p.deco.1.f P z) := by
  obtain ⟨s, hs, hsz⟩ := (mem_locP P.1 _ z).1 hz
  have h := hg.f P _ hsz i hi
  rw [Splice.adAt_pullV_osmul, p.deco.2.f_smul P s z hz] at h
  exact Splice.hasRes_of_mul hs h

theorem row_of_lat {n : ℕ} {g : GL (Fin n) (AfE F E)} {N : Submodule (𝓞 E) (Sp E n)}
    (hg : Formalism.L2.Herm.Carries g (stdLat E n) N) (T : AfE F E → Prop) (h0 : T 0) (hadd : ∀ a b, T a → T b → T (a + b))
    (hmul : ∀ c ∈ RInt F E, ∀ a, T a → T (c * a)) (c : Fin n → AfE F E)
    (h : ∀ z ∈ N, T (c ⬝ᵥ fun j => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (z j))) (s : Fin n) :
    T ((c ᵥ* (g : Matrix (Fin n) (Fin n) (AfE F E))) s) := by
  have key : ∀ u ∈ Formalism.L2.Herm.hatL (F := F) N, T (c ⬝ᵥ u) := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, hv, rfl⟩ := hx
      exact h v hv
    | zero => rwa [dotProduct_zero]
    | add x y _ _ hx hy =>
      rw [dotProduct_add]
      exact hadd _ _ hx hy
    | smul a x _ hx =>
      have e0 : a • x = (a : AfE F E) • x := rfl
      rw [e0, dotProduct_smul, smul_eq_mul]
      exact hmul _ a.2 _ hx
  have hu : (fun l => (g : Matrix (Fin n) (Fin n) (AfE F E)) l s) ∈ Formalism.L2.Herm.hatL (F := F) N := by
    refine (hg _).2 ((mem_latS_std _).2 fun l => ?_)
    simp only [Matrix.mulVec, dotProduct]
    rw [← Matrix.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  exact key _ hu

variable {a b : ℕ}

abbrev adMat (F : Type) [Field F] [NumberField F] [Algebra F E] (x : HomE E a b) : Matrix (Fin b) (Fin a) (AfE F E) :=
  (LinearMap.toMatrix' x).map (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F))

def mid (g : GL (Fin a) (AfE F E)) (g' : GL (Fin b) (AfE F E)) (x : HomE E a b) : Matrix (Fin b) (Fin a) (AfE F E) :=
  ((g'⁻¹ : GL (Fin b) (AfE F E)) : Matrix (Fin b) (Fin b) (AfE F E)) * adMat F x * (g : Matrix (Fin a) (Fin a) (AfE F E))

omit [StarRing E] in

theorem pullV_map (g' : GL (Fin b) (AfE F E)) (x : HomE E a b) (z : Sp E a) :
    Col2.pullV g' (x z) = (((g'⁻¹ : GL (Fin b) (AfE F E)) : Matrix (Fin b) (Fin b) (AfE F E)) * adMat F x) *ᵥ
      fun j => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (z j) := by
  unfold Col2.pullV
  rw [← Matrix.mulVec_mulVec]
  congr 1
  funext i
  rw [← LinearMap.toMatrix'_mulVec x z]
  exact RingHom.map_mulVec _ _ _ i

omit [StarRing E] in

theorem pullV_mid (g : GL (Fin a) (AfE F E)) (g' : GL (Fin b) (AfE F E)) (x : HomE E a b) (z : Sp E a) :
    Col2.pullV g' (x z) = mid g g' x *ᵥ Col2.pullV g z := by
  rw [pullV_map]
  unfold Col2.pullV mid
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc (_ * _), ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

def Good (P : HeightOneSpectrum (𝓞 E)) (ia : Fin a) (ib : Fin b) (X : Matrix (Fin b) (Fin a) (AfE F E)) : Prop :=
  (∀ r s, Valued.v (adAt F P (X r s)) ≤ 1) ∧ ∀ s, Valued.v (adAt F P (X ib s - (1 : Matrix (Fin a) (Fin a) (AfE F E)) ia s)) < 1

omit [StarRing E] in

theorem Good.congr {P : HeightOneSpectrum (𝓞 E)} {ia : Fin a} {ib : Fin b} {X Y : Matrix (Fin b) (Fin a) (AfE F E)}
    (h : Good P ia ib X) (hXY : ∀ r s, Valued.v (adAt F P (Y r s - X r s)) < 1) : Good P ia ib Y := by
  refine ⟨fun r s => ?_, fun s => ?_⟩
  · rw [← sub_add_cancel (Y r s) (X r s), map_add]
    exact Valuation.map_add_le _ (hXY r s).le (h.1 r s)
  · rw [← sub_add_sub_cancel (Y ib s) (X ib s), map_add]
    exact Valuation.map_add_lt _ (hXY ib s) (h.2 s)

variable {ST SG Q SG' Q' : Finset (HeightOneSpectrum (𝓞 E))}

theorem cond_iff {g : GL (Fin a) (AfE F E)} {g' : GL (Fin b) (AfE F E)} {p : DecoF E a ST SG Q} {p' : DecoF E b ST SG' Q'}
    (hg : IsPtOf hc g p) (hg' : IsPtOf hc g' p') (P : ST) {ia : Fin a} {ib : Fin b} (ha : ia.1 + 1 = a) (hb : ib.1 + 1 = b)
    (x : HomE E a b) :
    (∀ z ∈ p.deco.1.at P.1, x z ∈ p'.deco.1.at P.1 ∧ p'.deco.1.f P (x z) = p.deco.1.f P z) ↔ Good P.1 ia ib (mid g g' x) := by
  have hint : ∀ c ∈ RInt F E, Valued.v (adAt F P.1 c) ≤ 1 := fun c hc => (mem_rInt_iff F E _).1 hc P.1
  constructor
  · intro h
    refine ⟨fun r s => ?_, fun s => ?_⟩
    · refine row_of_lat hg.lat (fun t => Valued.v (adAt F P.1 t) ≤ 1) (by simp) (fun t t' ht ht' => ?_) (fun c hc t ht => ?_)
        ((((g'⁻¹ : GL (Fin b) (AfE F E)) : Matrix (Fin b) (Fin b) (AfE F E)) * adMat F x) r) (fun z hz => ?_) s
      · rw [map_add]
        exact Valuation.map_add_le _ ht ht'
      · rw [map_mul, map_mul]
        exact mul_le_one' (hint c hc) ht
      · have h1 := (mem_localization_iff p'.deco.2.lat hg'.lat P.1 _).1 (h z (le_locP _ _ hz)).1 r
        rw [pullV_map] at h1
        exact h1
    · have h2 := row_of_lat hg.lat (fun t => Valued.v (adAt F P.1 t) < 1) (by simp) (fun t t' ht ht' => ?_) (fun c hc t ht => ?_)
        ((((g'⁻¹ : GL (Fin b) (AfE F E)) : Matrix (Fin b) (Fin b) (AfE F E)) * adMat F x) ib -
          ((g⁻¹ : GL (Fin a) (AfE F E)) : Matrix (Fin a) (Fin a) (AfE F E)) ia) (fun z hz => ?_) s
      · rw [Matrix.sub_vecMul, Pi.sub_apply] at h2
        have e : (((g⁻¹ : GL (Fin a) (AfE F E)) : Matrix (Fin a) (Fin a) (AfE F E)) ia ᵥ* (g : Matrix (Fin a) (Fin a) (AfE F E))) s =
            (1 : Matrix (Fin a) (Fin a) (AfE F E)) ia s := by
          rw [← Units.val_one, ← inv_mul_cancel g, Units.val_mul]
          rfl
        rw [e] at h2
        exact h2
      · rw [map_add]
        exact Valuation.map_add_lt _ ht ht'
      · rw [map_mul, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint c hc)) ht
      · have hz' := le_locP P.1 _ hz
        have h1 := hasRes_f hg' P (h z hz').1 hb
        rw [(h z hz').2] at h1
        have h3 := PtStab.val_sub_lt_of_hasRes h1 (hasRes_f hg P hz' ha)
        rw [← map_sub, pullV_map] at h3
        rw [sub_dotProduct]
        exact h3
  · rintro ⟨h1, h2⟩ z hz
    have hw := (mem_localization_iff p.deco.2.lat hg.lat P.1 z).1 hz
    have hxz : x z ∈ p'.deco.1.at P.1 := by
      refine (mem_localization_iff p'.deco.2.lat hg'.lat P.1 _).2 fun r => ?_
      rw [pullV_mid g]
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
      exact Valuation.map_sum_le _ fun s _ => by
        rw [map_mul]
        exact mul_le_one' (h1 r s) (hw s)
    refine ⟨hxz, HasRes.unique (hasRes_f hg' P hxz hb) (PtStab.hasRes_of_sub (hasRes_f hg P hz ha) ?_)⟩
    have e : Col2.pullV g' (x z) ib - Col2.pullV g z ia =
        ∑ s, (mid g g' x ib s - (1 : Matrix (Fin a) (Fin a) (AfE F E)) ia s) * Col2.pullV g z s := by
      have e1 : Col2.pullV g z ia = ((1 : Matrix (Fin a) (Fin a) (AfE F E)) *ᵥ Col2.pullV g z) ia := by rw [Matrix.one_mulVec]
      rw [pullV_mid g, e1]
      simp only [Matrix.mulVec, dotProduct, _root_.sub_mul, Finset.sum_sub_distrib]
    rw [Valuation.map_sub_swap, ← map_sub, e, map_sum]
    refine Valuation.map_sum_lt _ one_ne_zero fun s _ => ?_
    rw [map_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hw s)) (h2 s)

omit [StarRing E] in

theorem val_mul_mul_lt (P : HeightOneSpectrum (𝓞 E)) {A : Matrix (Fin b) (Fin b) (AfE F E)} {D : Matrix (Fin b) (Fin a) (AfE F E)}
    {C : Matrix (Fin a) (Fin a) (AfE F E)} (hA : ∀ r s, Valued.v (adAt F P (A r s)) ≤ 1) (hD : ∀ r s, Valued.v (adAt F P (D r s)) < 1)
    (hC : ∀ r s, Valued.v (adAt F P (C r s)) ≤ 1) (r : Fin b) (s : Fin a) : Valued.v (adAt F P ((A * D * C) r s)) < 1 := by
  rw [Matrix.mul_apply, map_sum]
  refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
  rw [map_mul, map_mul]
  refine lt_of_le_of_lt (mul_le_of_le_one_right' (hC j s)) ?_
  rw [Matrix.mul_apply, map_sum]
  refine Valuation.map_sum_lt _ one_ne_zero fun l _ => ?_
  rw [map_mul, map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' (hA r l)) (hD l j)

theorem carries_one (n : ℕ) : Formalism.L2.Herm.Carries (1 : GL (Fin n) (AfE F E)) (stdLat E n) (stdLat E n) :=
  fun x => by simp

theorem phiT_eq (K : Type) [Field K] (ha : 0 < a) (hb : 0 < b) {k y : GL (Fin a) (AfE F E)} {k' y' : GL (Fin b) (AfE F E)}
    {p q : DecoF E a ST SG Q} {p' q' : DecoF E b ST SG' Q'}
    (hp : IsPtOf hc k p) (hpN : p.deco.1.N = stdLat E a) (hp' : IsPtOf hc k' p') (hpN' : p'.deco.1.N = stdLat E b)
    (hq : IsPtOf hc (y * k) q) (hq' : IsPtOf hc (y' * k') q') (x x₀ : HomE E a b)
    (h : ∀ P ∈ ST, ∀ r s, Valued.v (adAt F P ((mid y y' x - adMat F x₀) r s)) < 1) :
    phiT K p.deco.1 p'.deco.1 x₀ = phiT K q.deco.1 q'.deco.1 x := by
  let ia : Fin a := ⟨a - 1, by omega⟩
  let ib : Fin b := ⟨b - 1, by omega⟩
  have hia : ia.1 + 1 = a := by show a - 1 + 1 = a; omega
  have hib : ib.1 + 1 = b := by show b - 1 + 1 = b; omega
  have hd : mid (y * k) (y' * k') x - mid k k' x₀ =
      ((k'⁻¹ : GL (Fin b) (AfE F E)) : Matrix (Fin b) (Fin b) (AfE F E)) * (mid y y' x - adMat F x₀) *
        (k : Matrix (Fin a) (Fin a) (AfE F E)) := by
    unfold mid
    rw [_root_.mul_inv_rev, Units.val_mul, Units.val_mul, Matrix.mul_sub, Matrix.sub_mul]
    simp only [Matrix.mul_assoc]
  have key : ∀ P : ST, ((∀ z ∈ p.deco.1.at P.1, x₀ z ∈ p'.deco.1.at P.1 ∧ p'.deco.1.f P (x₀ z) = p.deco.1.f P z) ↔
      (∀ z ∈ q.deco.1.at P.1, x z ∈ q'.deco.1.at P.1 ∧ q'.deco.1.f P (x z) = q.deco.1.f P z)) := by
    intro P
    rw [cond_iff hp hp' P hia hib, cond_iff hq hq' P hia hib]
    have hlt : ∀ r s, Valued.v (adAt F P.1 (mid (y * k) (y' * k') x r s - mid k k' x₀ r s)) < 1 := by
      intro r s
      rw [← Matrix.sub_apply, hd]
      refine val_mul_mul_lt P.1 (fun r s => ?_) (h P.1 P.2) (fun r s => ?_) r s
      · have := Splice.valued_inv_mul_le (w := P.1) (hpN' ▸ hp'.lat) (carries_one (F := F) b) le_rfl r s
        rwa [mul_one] at this
      · have := Splice.valued_inv_mul_le (w := P.1) (carries_one (F := F) a) (hpN ▸ hp.lat) le_rfl r s
        rwa [inv_one, one_mul] at this
    refine ⟨fun hG => hG.congr hlt, fun hG => hG.congr fun r s => ?_⟩
    rw [map_sub, Valuation.map_sub_swap, ← map_sub]
    exact hlt r s
  unfold phiT
  have key' := forall_congr' key
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (key'.1 h1) h2
  · exact absurd (key'.2 h2) h1
  · rfl

omit [StarRing E] in

theorem val_natCast_lt {S : Finset (HeightOneSpectrum (𝓞 E))} {M : ℕ} (hM : (∏ P ∈ S, Ideal.absNorm P.asIdeal) ∣ M)
    {P : HeightOneSpectrum (𝓞 E)} (hP : P ∈ S) : Valued.v ((M : ℕ) : P.adicCompletion E) < 1 := by
  have e : ((M : ℕ) : P.adicCompletion E) = algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E ((M : ℕ) : 𝓞 E)) := by
    simp
  rw [e, valued_algebraMap]
  refine (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 ?_
  obtain ⟨c, rfl⟩ := (Finset.dvd_prod_of_mem _ hP).trans hM
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)

end Gen

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.Transport.LevelDatum
