import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdempotentComponentOfGroupElement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinPartAlgebraMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqSumFiniteCoordsOfInfinitePartZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open IsDedekindDomain NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitCut

variable {D : D7}

theorem cut_mul {R : Type} [CommRing R] {n : ℕ} (e f : R) (hef : e * f = 0) (M : Matrix (Fin n) (Fin n) R) :
    (e • M + (1 - e) • (1 : Matrix (Fin n) (Fin n) R)) * (f • M + (1 - f) • 1) = (e + f) • M + (1 - (e + f)) • 1 := by
  have h1 : e * (1 - f) = e := by rw [mul_sub, mul_one, hef, sub_zero]
  have h2 : (1 - e) * f = f := by rw [sub_mul, one_mul, hef, sub_zero]
  have h3 : (1 - e) * (1 - f) = 1 - (e + f) := by linear_combination hef
  simp only [add_mul, mul_add, smul_mul_smul_comm, Matrix.mul_one, Matrix.one_mul, hef, h1, h2, h3, zero_smul, zero_add]
  rw [add_smul]; abel

theorem mt_mul (V : HSp D) (x y : GA D V) : mt V (x * y) = mt V x * mt V y := by
  show (matHom V (x * y)).1 = (matHom V x).1 * (matHom V y).1
  rw [map_mul, Units.val_mul]

theorem mt_one (V : HSp D) : mt V 1 = 1 := by
  show (matHom V 1).1 = 1
  rw [map_one, Units.val_one]

theorem mt_injective (V : HSp D) : Function.Injective (mt V) := by
  intro x y h
  exact Subtype.ext (Units.ext h)

theorem cA_algebraMap (a : AF D.host.F) : cA D (algebraMap (AF D.host.F) (AE D) a) = algebraMap (AF D.host.F) (AE D) a := by
  show (Algebra.TensorProduct.map (AlgHom.id D.host.F (AF D.host.F)) (D.sp.cm.sig)).toRingHom (a ⊗ₜ 1) = a ⊗ₜ 1
  simp

theorem cut_exists (V : HSp D) (g : GA D V) (ε : AE D) (hεε : ε * ε = ε) (hε : cA D ε = ε) :
    ∃ k : GA D V, mt V k = ε • mt V g + (1 - ε) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  set M := mt V g with hM
  have hinv : M * ((matHom V g)⁻¹).1 = 1 := (matHom V g).mul_inv
  have hinv' : ((matHom V g)⁻¹).1 * M = 1 := (matHom V g).inv_mul
  let K : GL (Fin V.rank) (AE D) := ⟨ε • M + (1 - ε) • 1, ε • ((matHom V g)⁻¹).1 + (1 - ε) • 1,
    GlobalTheory.GfCut.idem_mul ε hεε _ _ hinv, GlobalTheory.GfCut.idem_mul ε hεε _ _ hinv'⟩
  have hgU : Formalism.UG.cT (cA D) M * V.gram.map (incA D) * M = V.gram.map (incA D) :=
    (show HR (AF D.host.F) D.sp.cm.sig V.gram from g).2
  have hKU : K ∈ HR (AF D.host.F) D.sp.cm.sig V.gram :=
    GlobalTheory.GfCut.idem_unitary (cA D) ε hε hεε _ M hgU
  exact ⟨(⟨K, hKU⟩ : HR (AF D.host.F) D.sp.cm.sig V.gram), rfl⟩

theorem entry_mem (V : HSp D) (P : Pl D → Prop) (g : GA D V) (hg : g ∈ grpOff V P) (i j : Fin V.rank) (u : Pl D) (hu : P u) :
    compAt D u ((mt V g - 1) i j) = 0 := by
  have h := congrArg (fun x : GL (Fin V.rank) (AE D ⧸ idOff D P) => x.1 i j) (show _ = (1 : GL _ _) from hg)
  change Ideal.Quotient.mk (idOff D P) (mt V g i j) = _ at h
  have h2 : Ideal.Quotient.mk (idOff D P) (mt V g i j) =
      Ideal.Quotient.mk (idOff D P) ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) := by
    rw [h, Units.val_one]; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have h4 : (mt V g - 1) i j ∈ idOff D P := by
    rw [Matrix.sub_apply]; exact Ideal.Quotient.eq.mp h2
  unfold idOff at h4
  rw [Ideal.mem_iInf] at h4
  exact (RingHom.mem_ker).mp (h4 ⟨u, hu⟩)

open GlobalTheory.LocWeil.PlaceIdem in
theorem eFin_of_placeIdem {v : Pl D} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) : ε = eFin D.host.F v := by
  obtain ⟨α, rfl, h1, h2⟩ := h
  unfold eFin
  congr 1
  refine af_ext _ fun u => ?_
  by_cases hu : u = v
  · subst hu; rw [h1, evalV_single_same]
  · rw [h2 u hu, evalV_single_ne _ hu]

open GlobalTheory.LocWeil.PlaceIdem in
theorem eFin_idem (v : Pl D) : eFin D.host.F v * eFin D.host.F v = eFin D.host.F v := by
  refine Prod.ext (mul_zero _) ?_
  change singleV D.host.F v 1 * singleV D.host.F v 1 = singleV D.host.F v 1
  refine af_ext _ fun u => ?_
  rw [map_mul]
  by_cases hu : u = v
  · subst hu; rw [evalV_single_same, mul_one]
  · rw [evalV_single_ne _ hu, mul_zero]

theorem compAt_eq (u : Pl D) (y : AE D) : compAt D u y = Algebra.TensorProduct.map (evalV D.host.F u) (AlgHom.id D.host.F D.host.E)
      (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) y) := rfl

theorem baseAdele_ext_infinite_finite {a b : AF D.host.F} (h1 : fstA D.host.F a = fstA D.host.F b) (h2 : sndA D.host.F a = sndA D.host.F b) :
    a = b := Prod.ext h1 h2

open GlobalTheory.LocWeil.PlaceIdem in
theorem c_mul {W : Type} [Fintype W] (v : W → Pl D) (hv : Function.Injective v) (a : AF D.host.F)
    (ha : ∀ u, u ∉ Set.range v → evalV D.host.F u (sndA D.host.F a) = 0) :
    (1 - pairA D.host.F 1 0 - ∑ w, eFin D.host.F (v w)) * a = 0 := by
  classical
  have hf : ∀ w, fstA D.host.F (eFin D.host.F (v w)) = 0 := fun w => rfl
  have hs : ∀ w, sndA D.host.F (eFin D.host.F (v w)) = singleV D.host.F (v w) 1 := fun w => rfl
  have hp1 : fstA D.host.F (pairA D.host.F 1 0) = 1 := rfl
  have hp2 : sndA D.host.F (pairA D.host.F 1 0) = 0 := rfl
  refine baseAdele_ext_infinite_finite ?_ ?_
  · rw [map_mul, map_zero, map_sub, map_sub, map_sum, map_one, hp1]
    simp [hf]
  · rw [map_mul, map_zero, map_sub, map_sub, map_sum, map_one, hp2]
    simp only [hs, sub_zero]
    refine af_ext _ fun u => ?_
    rw [map_mul, map_zero, map_sub, map_one, map_sum]
    by_cases hu : u ∈ Set.range v
    · obtain ⟨w0, rfl⟩ := hu
      rw [Finset.sum_eq_single w0 (fun w _ hw => evalV_single_ne _ (fun e => hw (hv e).symm))
        (by simp), evalV_single_same, sub_self, zero_mul]
    · rw [ha u hu, mul_zero]

theorem repr_zero2 {F E A A' A'' ι : Type} [Field F] [CommRing E] [Algebra F E] [CommRing A] [Algebra F A]
    [CommRing A'] [Algebra F A'] [CommRing A''] [Algebra F A''] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)
    (f : A →ₐ[F] A') (g : A' →ₐ[F] A'') (y : A ⊗[F] E)
    (hy : Algebra.TensorProduct.map g (AlgHom.id F E) (Algebra.TensorProduct.map f (AlgHom.id F E) y) = 0) (k : ι) :
    g (f ((Algebra.TensorProduct.basis A b).repr y k)) = 0 := by
  rw [← GlobalTheory.InfZeroFinSum.repr_map_id b f, ← GlobalTheory.InfZeroFinSum.repr_map_id b g, hy, map_zero, Finsupp.zero_apply]

theorem key_gen {F E A ι : Type} [Field F] [CommRing E] [Algebra F E] [CommRing A] [Algebra F A]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E) (c : A) (y : A ⊗[F] E)
    (hy : ∀ k, c * (Algebra.TensorProduct.basis A b).repr y k = 0) : algebraMap A (A ⊗[F] E) c * y = 0 := by
  refine (Algebra.TensorProduct.basis A b).ext_elem fun k => ?_
  rw [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.zero_apply]
  exact hy k

open GlobalTheory.LocWeil.PlaceIdem in
theorem key {W : Type} [Fintype W] (v : W → Pl D) (hv : Function.Injective v) (y : AE D)
    (hy : ∀ u, u ∉ Set.range v → compAt D u y = 0) :
    algebraMap (AF D.host.F) (AE D) (1 - pairA D.host.F 1 0 - ∑ w, eFin D.host.F (v w)) * y = 0 := by
  refine key_gen (Module.finBasis D.host.F D.host.E) _ y fun k => c_mul v hv _ fun u hu => ?_
  exact repr_zero2 (Module.finBasis D.host.F D.host.E) (sndA D.host.F) (evalV D.host.F u) y ((compAt_eq u y).symm.trans (hy u hu)) k

theorem idempotent_mul_entry_eq_zero_of_cut_inverse {R : Type} [CommRing R] {n : ℕ} (E : R) (hE : E * E = E) (M N : Matrix (Fin n) (Fin n) R)
    (h1 : (E • M + (1 - E) • (1 : Matrix (Fin n) (Fin n) R)) * N = 1) (i j : Fin n) : E * (M * N - 1) i j = 0 := by
  have h2 : E • (M * N) = E • (1 : Matrix (Fin n) (Fin n) R) := by
    have h3 := congrArg (fun X => E • X) h1
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, smul_add, smul_smul, hE] at h3
    have h4 : E * (1 - E) = 0 := by rw [mul_sub, mul_one, hE, sub_self]
    rw [h4, zero_smul, add_zero] at h3
    exact h3
  have := congrArg (fun X => X i j) h2
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  rw [Matrix.sub_apply, mul_sub, this, sub_self]

theorem idempotent_mul_cut_sub_one_entry {R : Type} [CommRing R] {n : ℕ} (E : R) (hE : E * E = E) (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    E * (E • M + (1 - E) • (1 : Matrix (Fin n) (Fin n) R) - 1) i j = (E • M + (1 - E) • (1 : Matrix (Fin n) (Fin n) R) - 1) i j := by
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  linear_combination (M i j - (1 : Matrix (Fin n) (Fin n) R) i j) * hE

theorem exists_widePullback_of_iteratedLine {R : Type} [CommRing R] {n : ℕ} (t : R) (M : Matrix (Fin n) (Fin n) R)
    (hk : ∀ i j, (1 - t) * (M - 1) i j = 0) : M = t • M + (1 - t) • (1 : Matrix (Fin n) (Fin n) R) := by
  ext i j
  have := hk i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply] at this ⊢
  linear_combination this

theorem mt_list_prod (V : HSp D) {W : Type} (h : W → GA D V) (E : W → AE D)
    (M : Matrix (Fin V.rank) (Fin V.rank) (AE D))
    (hh : ∀ w, mt V (h w) = E w • M + (1 - E w) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)))
    (horth : ∀ w w', w ≠ w' → E w * E w' = 0) :
    ∀ l : List W, l.Nodup → mt V ((l.map h).prod) = (l.map E).sum • M + (1 - (l.map E).sum) • 1
  | [], _ => by simp [mt_one]
  | w :: l, hl => by
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons, mt_mul, mt_list_prod V h E M hh horth l hl.2, hh, List.map_cons,
      List.sum_cons]
    apply cut_mul
    rw [← List.sum_map_mul_left]
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact horth w y (fun e => hl.1 (e ▸ hy))

set_option maxHeartbeats 800000 in
open GlobalTheory.LocWeil.PlaceIdem in

theorem prod_of_trivOff : ∀ (D : D7) (V : HSp D) (W : Type) [Fintype W] [DecidableEq W] (v : W → Pl D) (e : W → AE D),
    Function.Injective v → (∀ w, IsSplitIdem D (e w) ∧ ∃ ε, IsPlaceIdem D (v w) ε ∧
      e w + cA D (e w) = algebraMap (AF D.host.F) (AE D) ε) →
    ∀ g ∈ grpOff V (fun x => x ∉ Set.range v), ∃ a ∈ GinfC V, ∃ h : W → GA D V, (∀ w, SuppAt (e w) V (h w)) ∧
      (∀ w w', w ≠ w' → Commute (h w) (h w')) ∧ (∀ w, Commute a (h w)) ∧
      g = a * (Finset.univ.toList.map h).prod ∧
      ∀ w, ∀ i j, (e w + cA D (e w)) * (mt V (g * (h w)⁻¹) - 1) i j = 0 := by
  intro D V W _ _ v e hv he g hg
  set E : W → AE D := fun w => algebraMap (AF D.host.F) (AE D) (eFin D.host.F (v w)) with hEdef
  have hE : ∀ w, e w + cA D (e w) = E w := fun w => by
    obtain ⟨_, ε, hε, h⟩ := he w
    rw [h, eFin_of_placeIdem hε]
  have hEE : ∀ w, E w * E w = E w := fun w => by
    simp only [hEdef, ← map_mul, eFin_idem]
  have hEc : ∀ w, cA D (E w) = E w := fun w => cA_algebraMap _
  have hEo : ∀ w w', w ≠ w' → E w * E w' = 0 := fun w w' hww => by
    simp only [hEdef, ← map_mul]
    rw [eFin_mul_eFin _ (fun h => hww (hv h)), map_zero]
  set r : AE D := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0) with hrdef
  have hrr : r * r = r := by
    rw [hrdef, ← map_mul]
    congr 1
    exact baseAdele_ext_infinite_finite (by rw [map_mul]; exact mul_one _) (by rw [map_mul]; exact mul_zero _)
  have hrE : ∀ w, r * E w = 0 := fun w => by
    rw [hrdef, hEdef, ← map_mul]
    have : pairA D.host.F 1 0 * eFin D.host.F (v w) = 0 :=
      baseAdele_ext_infinite_finite (by rw [map_mul, map_zero]; exact mul_zero _) (by rw [map_mul, map_zero]; exact zero_mul _)
    rw [this, map_zero]
  choose h hh using fun w => cut_exists V g (E w) (hEE w) (hEc w)
  obtain ⟨a, ha⟩ := cut_exists V g r hrr (cA_algebraMap _)
  set M := mt V g with hM
  have hsum : (Finset.univ.toList.map E).sum = ∑ w, E w := Finset.sum_map_toList _ _
  refine ⟨a, ?_, h, ?_, ?_, ?_, ?_, ?_⟩
  · show finHom V a = 1
    have h0 : finPart D r = 0 := by
      rw [hrdef, finPart_algebraMap]
      exact TensorProduct.zero_tmul _ _
    apply Units.ext
    change (mt V a).map (finPart D) = 1
    rw [ha, GlobalTheory.GfCut.map_idem, h0, zero_smul, zero_add, sub_zero, one_smul]
  · intro w i j
    rw [hE w, hh w]
    exact idempotent_mul_cut_sub_one_entry _ (hEE w) M i j
  · intro w w' hww
    show h w * h w' = h w' * h w
    apply mt_injective
    rw [mt_mul, mt_mul, hh, hh, cut_mul _ _ (hEo w w' hww), cut_mul _ _ (hEo w' w (Ne.symm hww)), add_comm (E w)]
  · intro w
    show a * h w = h w * a
    apply mt_injective
    rw [mt_mul, mt_mul, hh, ha, cut_mul _ _ (hrE w), cut_mul _ _ (by rw [mul_comm]; exact hrE w), add_comm r]
  · apply mt_injective
    rw [mt_mul, mt_list_prod V h E M hh hEo _ (Finset.nodup_toList _), ha, hsum]
    have hrS : r * ∑ w, E w = 0 := by
      rw [Finset.mul_sum]; exact Finset.sum_eq_zero fun w _ => hrE w
    rw [cut_mul _ _ hrS]
    have hk : ∀ i j, (1 - r - ∑ w, E w) * (M - 1) i j = 0 := fun i j => by
      have := key v hv ((M - 1) i j) (fun u hu => entry_mem V _ g hg i j u hu)
      rwa [map_sub, map_sub, map_one, map_sum] at this
    exact exists_widePullback_of_iteratedLine _ M fun i j => by rw [← sub_sub]; exact hk i j
  · intro w i j
    rw [hE w]
    have h1 : (E w • M + (1 - E w) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) * mt V (h w)⁻¹ = 1 := by
      rw [← hh w, ← mt_mul, mul_inv_cancel, mt_one]
    rw [mt_mul]
    exact idempotent_mul_entry_eq_zero_of_cut_inverse _ (hEE w) _ _ h1 i j

end GlobalTheory.SplitCut
