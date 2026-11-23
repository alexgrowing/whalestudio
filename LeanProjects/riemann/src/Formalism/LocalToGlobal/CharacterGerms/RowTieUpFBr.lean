import Formalism.LocalToGlobal.CharacterGerms.RowTieUpF
import Formalism.LocalToGlobal.CharacterGerms.RowTiePFBMapSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace UpFBr

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ CharacteristicFromRanks ValuationFitting
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (IsCh dl res HasAF)

section Series

variable {C : Type} [Field C] [CharZero C] {V : VF C} {OE : Type} [CommRing OE] [StarRing OE] {dd : ℕ}
variable {R : Type} [CommRing R] [Algebra R C]

abbrev toC {n : ℕ} (f : PS R n dd) : PS C n dd := MvPowerSeries.map (algebraMap R C) f

theorem mpt_pt {n : ℕ} (j : Fin n) : MapFB.mpt (algebraMap R C) (pt R dd j) = pt C dd j := by
  funext i
  simp [MapFB.mpt, pt]

theorem cc_pt {n : ℕ} (j : Fin n) (i : Fin dd) : MvPowerSeries.constantCoeff (pt R dd j i) = 0 := by
  simp [pt]

theorem isChar_of_isCh (Y : FBChart C V OE dd) (hR : ∀ x : R, V.Ge 0 (algebraMap R C x))
    (FR : Fin dd → PS R 2 dd) (hF : ∀ i, Y.B.G.F i = toC (FR i))
    (hF0 : ∀ i, MvPowerSeries.constantCoeff (FR i) = 0) {u : PS R 1 dd} (hu : IsCh FR u) :
    Y.IsChar (toC u) := by
  refine ⟨fun μ => ?_, ?_, ?_⟩
  · rw [MvPowerSeries.coeff_map]; exact hR _
  · rw [MvPowerSeries.constantCoeff_map, hu.1, map_one]
  · have h := congrArg (MvPowerSeries.map (algebraMap R C)) hu.2
    have hadd : ∀ i, MvPowerSeries.constantCoeff (addOf FR (pt R (n := 2) dd 0) (pt R (n := 2) dd 1) i) = 0 := by
      intro i
      refine MapFB.cc_ev _ ?_ _ (hF0 i)
      intro j i'
      fin_cases j <;> simp [pt]
    rw [map_mul, MapFB.map_ev1 _ _ hadd, MapFB.map_ev1 _ _ (cc_pt 0), MapFB.map_ev1 _ _ (cc_pt 1), mpt_pt, mpt_pt] at h
    have e : MapFB.mpt (algebraMap R C) (addOf FR (pt R (n := 2) dd 0) (pt R (n := 2) dd 1)) =
        addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1) := by
      funext i
      show MvPowerSeries.map (algebraMap R C) (ev ![pt R (n := 2) dd 0, pt R (n := 2) dd 1] (FR i)) = _
      rw [MapFB.map_ev2 _ _ _ (cc_pt 0) (cc_pt 1), mpt_pt, mpt_pt]
      show _ = ev ![pt C (n := 2) dd 0, pt C (n := 2) dd 1] (Y.B.G.F i)
      rw [hF i]
    rw [e] at h
    exact h

theorem dlogC_toC (u : PS R 1 dd) (i : Fin dd) : dlogC (toC u) i = algebraMap R C (dl u i) := by
  unfold dlogC dl
  rw [MvPowerSeries.coeff_map]

end Series

section Len

theorem lenCoker_mono {R : Type} [CommRing R] (v : AddValuation R (WithTop ℝ)) {m h h' : ℕ}
    (B : Matrix (Fin m) (Fin h') R) (f : Fin h → Fin h') :
    S4.lenCoker v B ≤ S4.lenCoker v (B.submatrix id f) := by
  unfold S4.lenCoker
  refine Finset.le_inf fun g _ => ?_
  exact Finset.inf_le (f := fun g : Fin m → Fin h' => v (B.submatrix id g).det) (Finset.mem_univ (f ∘ g))

variable {C : Type} [Field C] {V : VF C} {vm : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C] {dd : ℕ}

theorem lenCoker_le_of_hasLen (hT : ValTie V vm) (hv : vm.Integers R) (h0 : 0 < (vm (V.l : C) : ℝ))
    (h1 : (vm (V.l : C) : ℝ) < 1) {s N : ℕ} (W : Fin s → Fin dd → R) (u : Fin N → PS R 1 dd) {x : NNReal}
    (hx : ReciprocityTheory.PGsh.Up.HasLen vm R
      ((Fin s → R) ⧸ Submodule.span R (Set.range fun k => res W (dl (u k)))) x)
    {S : ℝ} (hS : vm (V.l : C) ^ S ≤ x) :
    S4.lenCoker V.v (Matrix.of fun c k => ∑ i, dlogC (toC (C := C) (u k)) i * algebraMap R C (W c i)) ≤
      ((S : ℝ) : WithTop ℝ) := by
  set α : Matrix (Fin s) (Fin N) R := Matrix.of fun c k => res W (dl (u k)) c with hα
  have hr : LinearMap.range α.mulVecLin = Submodule.span R (Set.range fun k => res W (dl (u k))) := by
    rw [Matrix.range_mulVecLin]
    rfl
  rw [← hr] at hx
  have hSr : (vm (V.l : C) : ℝ) ^ S ≤ (x : ℝ) := by exact_mod_cast hS
  have hpos : 0 < (x : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos h0 S) hSr
  have e := lenCoker_eq_logb hT hv h0 h1 α hx hpos
  have e2 : (Matrix.of fun c k => ∑ i, dlogC (toC (C := C) (u k)) i * algebraMap R C (W c i)) =
      Matrix.of fun c k => algebraMap R C (α c k) := by
    ext c k
    simp only [Matrix.of_apply, hα, res, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, map_sum, map_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e2, e]
  refine WithTop.coe_le_coe.mpr ?_
  have h2 : Real.logb (vm (V.l : C) : ℝ) x ≤ Real.logb (vm (V.l : C) : ℝ) ((vm (V.l : C) : ℝ) ^ S) :=
    (Real.logb_le_logb_of_base_lt_one h0 h1 hpos (Real.rpow_pos_of_pos h0 S)).mpr hSr
  rwa [Real.logb_rpow h0 (ne_of_lt h1)] at h2

end Len

section Sum

theorem frobSum_conj_alt {d : ℕ} {l : ℕ} (hl : 1 < l) (n j j' : ℕ) (big : ZMod d → Prop)
    (halt : ∀ b, big (b + 1) ↔ ¬ big b) (q : ZMod d → ℕ)
    (hqb : ∀ b, big b → q b = j') (hqs : ∀ b, ¬ big b → q b = n + j) (a : ZMod d) (ha : big a) :
    S4.frobSum l q a = upB l (n + j) j' (gam l) := by
  rw [S4.frobSum_alt hl j' 0 (n + j) big halt q (fun b hb => by rw [hqb b hb]; rfl) hqs a ha]
  have h1 := S4.one_div_eq_gam_add_rho hl
  have hg : gam l = S4.gam l := rfl
  have hdiv : (j' : ℝ) / ((l : ℝ) - 1) = j' * (S4.gam l + S4.rho l) := by rw [← h1]; ring
  unfold upB
  rw [hg, hdiv]
  push_cast
  ring

theorem frobSum_conj_all {d : ℕ} {l : ℕ} (hl : 1 < l) (n j j' : ℕ) (q : ZMod d → ℕ) (hq : ∀ b, q b = j')
    (a : ZMod d) : S4.frobSum l q a = upB l (n + j) j' 0 := by
  rw [S4.frobSum_const hl j' q hq a]
  unfold upB
  ring

end Sum

section Core

variable {C : Type} [Field C] [CharZero C] {V : VF C} {OE : Type} [CommRing OE] [StarRing OE] {dd : ℕ} {d : ℕ} [NeZero d]
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]

def rk {Y : FBChart C V OE dd} (p : PairData Y d I) (g : Fin 2) (b : ZMod d) : ℕ :=
  (Finset.univ.filter fun c : I g => p.ty g c = b).card

def AFBound (Y : FBChart C V OE dd) (p : PairData Y d I) (vm : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C]
    (FR : Fin dd → PS R 2 dd) : Prop :=
  ∀ g a, p.big g a → ∃ (s : ℕ) (e : Fin s ≃ {x : I g // p.ty g x = a}) (W : Fin s → Fin dd → R) (xs : NNReal),
    (∀ c i, algebraMap R C (W c i) = p.u g (e c) i) ∧ HasAF vm FR W xs ∧
      vm (V.l : C) ^ (S4.frobSum V.l (rk p (1 - g)) a) ≤ xs

theorem upChar_of_afBound (Y : FBChart C V OE dd) (p : PairData Y d I) (hr : (Y.raw p).RankHyp)
    (Hc : ∀ g, (Y.raw p).CartHyp V g) (vm : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C]
    (hT : ValTie V vm) (hv : vm.Integers R) (h0 : 0 < (vm (V.l : C) : ℝ)) (h1 : (vm (V.l : C) : ℝ) < 1)
    (FR : Fin dd → PS R 2 dd) (hF : ∀ i, Y.B.G.F i = toC (FR i))
    (hF0 : ∀ i, MvPowerSeries.constantCoeff (FR i) = 0) (h : AFBound Y p vm R FR) : UPCharSt Y p Hc := by
  have hR : ∀ x : R, V.Ge 0 (algebraMap R C x) := fun x => vA_nonneg hT hv h0 h1 x
  have hl1 : 1 < V.l := V.l_prime.one_lt
  have key : ∀ g a, ∃ (N : ℕ) (u : Fin N → PS C 1 dd), (∀ k, Y.IsChar (u k)) ∧ (p.big g a →
      ∃ e : Fin (pT (fun g => RawChart.cart (Hc g)) g a) ≃ {x : I g // (RawChart.cart (Hc g)).ty (Sum.inl x) = a},
        S4.lenCoker V.v (Matrix.of fun c k => p.yOf g (u k) (e c)) ≤
          ((S4.frobSum V.l (rk p (1 - g)) a : ℝ) : WithTop ℝ)) := by
    intro g a
    by_cases hb : p.big g a
    · obtain ⟨s, e, W, xs, hW, ⟨N, u, hu, hx⟩, hS⟩ := h g a hb
      have hs : s = pT (fun g => RawChart.cart (Hc g)) g a := by
        have := Fintype.card_congr e
        rw [Fintype.card_fin, Fintype.card_subtype] at this
        exact this
      subst hs
      refine ⟨N, fun k => toC (u k), fun k => isChar_of_isCh Y hR FR hF hF0 (hu k), fun _ => ⟨e, ?_⟩⟩
      have := lenCoker_le_of_hasLen hT hv h0 h1 W u hx hS
      simp only [hW] at this
      exact this
    · exact ⟨0, fun k => k.elim0, fun k => k.elim0, fun hb' => absurd hb' hb⟩
  choose N u hu he using key
  let eq : ∀ g, (Σ a : ZMod d, Fin (N g a)) ≃ Fin (Fintype.card (Σ a : ZMod d, Fin (N g a))) := fun g => Fintype.equivFin _
  refine ⟨fun g => Fintype.card (Σ a : ZMod d, Fin (N g a)),
    fun g i => u g ((eq g).symm i).1 ((eq g).symm i).2, fun g i => hu g _ _, fun g a hb => ?_⟩
  obtain ⟨e, hle⟩ := he g a hb
  have hle' : S4.lenCoker V.v (Matrix.of fun c i => p.yOf g (u g ((eq g).symm i).1 ((eq g).symm i).2) (e c)) ≤
      ((S4.frobSum V.l (rk p (1 - g)) a : ℝ) : WithTop ℝ) := by
    refine le_trans (lenCoker_mono V.v _ (fun k : Fin (N g a) => eq g ⟨a, k⟩)) ?_
    have e3 : (Matrix.of fun c i => p.yOf g (u g ((eq g).symm i).1 ((eq g).symm i).2) (e c)).submatrix id
        (fun k : Fin (N g a) => eq g ⟨a, k⟩) = Matrix.of fun c k => p.yOf g (u g a k) (e c) := by
      ext c k
      simp only [Matrix.submatrix_apply, Matrix.of_apply, id]
      rw [Equiv.symm_apply_apply]
    rw [e3]
    exact hle
  have hc1 : ∀ b, p.big g b → rk p (1 - g) b = p.j' := fun b hb' =>
    hr.rk_small (1 - g) b (fun hh => (hr.big_compl g b).mp hh hb')
  have hc2 : ∀ b, ¬ p.big g b → rk p (1 - g) b = p.n + p.j := fun b hb' =>
    hr.rk_big (1 - g) b ((hr.big_compl g b).mpr hb')
  refine ⟨e, fun hA => ?_, fun hB => ?_⟩
  · rw [← frobSum_conj_alt hl1 p.n p.j p.j' (p.big g) (alt_step p.big hr.big_compl hA g) (rk p (1 - g)) hc1 hc2 a hb]
    exact hle'
  · rw [← frobSum_conj_all hl1 p.n p.j p.j' (rk p (1 - g)) (fun b => hc1 b (hB b)) a]
    exact hle'

end Core

end UpFBr

end Formalism.L2.FormalSeriesBounds
