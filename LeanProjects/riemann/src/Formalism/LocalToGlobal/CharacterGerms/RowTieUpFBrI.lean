import Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBr

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace UpFBr

open Formalism.IncomingBounds CharacteristicFromRanks ValuationFitting
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF IsLocalRing

attribute [local instance] Over.cartesianMonoidalCategory

def GeoJ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G]
    (OE : Type) [CommRing OE] [StarRing OE] (aG : OE → (G ⟶ G)) (dd : ℕ) (FT : Fin dd → PS T 2 dd)
    (actT : OE → Fin dd → PS T 1 dd) : Prop :=
  ∃ (D : Out.DegData T (maximalIdeal T)) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing T))))
    (U : Out.UnifPre (maximalIdeal T) D A G) (F : FGLaw T dd)
    (x : ∀ m : ℕ, algOver T (JetR T (Fin 1 × Fin dd) m) ⟶ G) (_ : Module OE D.toPre.X) (io : Out.RingAct G OE)
    (oD : D.OAct OE) (oA : A.OAct OE) (act : Germ.OAct OE F),
    F.F = FT ∧ act.act = actT ∧ (∀ a, io.act a = aG a) ∧ IsChartJ G F x ∧ U.OLinear OE oD oA io ∧
      ChartActs G x io act

def PlaceIn (l : ℕ) [Fact l.Prime] (OE : Type) [CommRing OE] (R : Type) [CommRing R] [Algebra ℤ_[l] R] (d : ℕ)
    (em : ZMod d → OE →+* R) : Prop :=
  ∃ (w : PlaceU l OE) (_ : NeZero w.n) (t : Fin w.n ≃ Emb (O := R) w.e) (jj : ZMod d ≃ Fin w.n),
    (∀ a, jj (a + 1) = jj a + 1) ∧ (∀ a, ((t (jj a) : Emb (O := R) w.e) : OE →+* R) = em a) ∧
    ∃ b : Module.Basis (Fin w.n) ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] w.e)),
      IsUnit (Matrix.det (Matrix.of fun i j =>
        tauExt ((t j : Emb (O := R) w.e) : OE →+* R) (b i : ℤ_[l] ⊗[ℤ] OE)))

def UpFLaw (p : ℕ) [Fact p.Prime] (T : Type) [CommRing T] (OE : Type) [CommRing OE] [StarRing OE] (dd : ℕ)
    (FT : Fin dd → PS T 2 dd) (actT : OE → Fin dd → PS T 1 dd) : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [Algebra O C], v.Integers O →
    ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsLocalRing O]
      [Algebra ℤ_[p] O] (iota : T →+* O), IsLocalHom iota →
    ∀ (w : PlaceU p OE) [NeZero w.n] (t : Fin w.n ≃ Emb (O := O) w.e),
    (∃ b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)),
      IsUnit (Matrix.det (Matrix.of fun i j =>
        tauExt ((t j : Emb (O := O) w.e) : OE →+* O) (b i : ℤ_[p] ⊗[ℤ] OE)))) →
    (∀ (j : Fin w.n) (a : OE), ((t (j + 1) : Emb (O := O) w.e) : OE →+* O) a -
        (((t j : Emb (O := O) w.e) : OE →+* O) a) ^ p ∈ maximalIdeal O) →
    ∀ (r : (OE →+* O) → ℕ) (W : ∀ τ : OE →+* O, Fin (r τ) → Fin dd → O),
      (∀ τ, IsEigBasis (fun a i => MvPowerSeries.map iota (actT a i)) τ (W τ)) →
    ∀ j : Fin w.n, ∃ xs : NNReal,
      HasAF v (fun i => MvPowerSeries.map iota (FT i)) (W ((t j : Emb (O := O) w.e) : OE →+* O)) xs ∧
      v (algebraMap O C (p : O)) ^ (∑' n : ℕ, ((p : ℝ) ^ (-((n : ℝ) + 1))) *
        (r (((t (j + Fin.ofNat w.n (n + 1)) : Emb (O := O) w.e) : OE →+* O).comp
          ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom) : ℝ)) ≤ xs

theorem upFLaw_of_geoJ {p : ℕ} [Fact p.Prime] (hUp : UpFSt p) (hp2 : p ≠ 2)
    (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [IsNoetherianRing T] [CharZero T]
    [IsAdicComplete (maximalIdeal T) T] (hlT : ¬ IsUnit (p : T))
    (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G]
    {OE : Type} [CommRing OE] [StarRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE]
    (aG : OE → (G ⟶ G)) {dd : ℕ} (FT : Fin dd → PS T 2 dd)
    (actT : OE → Fin dd → PS T 1 dd) (hG : GeoJ T G OE aG dd FT actT)
    (hdisc : ¬ ((p : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE))) : UpFLaw p T OE dd FT actT := by
  obtain ⟨D, A, U, F, x, iM, io, oD, oA, act, rfl, rfl, -, hx, hO, hA⟩ := hG
  intro C _ _ _ v O _ _ hv _ _ _ _ iota hloc w _ t hbas hfrob r W hW j
  exact hUp T hlT G D A U dd F x hx hp2 OE io oD oA hO hdisc act hA C v O hv iota hloc w t hbas hfrob r W hW j

section Inst

variable {C : Type} [Field C] [CharZero C] {V : VF C} {OE : Type} [CommRing OE] [StarRing OE] {dd : ℕ} {d : ℕ} [NeZero d]
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]

def EigIn {Y : FBChart C V OE dd} (p : PairData Y d I) (R : Type) [CommRing R] [Algebra R C]
    (actR : OE → Fin dd → PS R 1 dd) (emR : Fin 2 → ZMod d → OE →+* R) : Prop :=
  ∃ (r : (OE →+* R) → ℕ) (W : ∀ τ : OE →+* R, Fin (r τ) → Fin dd → R), (∀ τ, IsEigBasis actR τ (W τ)) ∧
    ∀ g a, ∃ e : Fin (r (emR g a)) ≃ {x : I g // p.ty g x = a},
      ∀ c i, algebraMap R C (W (emR g a) c i) = p.u g (e c) i

theorem ofNat_succ (n : ℕ) [NeZero n] (k : ℕ) : Fin.ofNat n (k + 1) = Fin.ofNat n k + 1 := by
  apply Fin.ext
  simp [Fin.ofNat, Fin.val_add, Nat.add_mod]

theorem jj_add {n : ℕ} [NeZero n] (jj : ZMod d ≃ Fin n) (h : ∀ a, jj (a + 1) = jj a + 1) (a : ZMod d) :
    ∀ k : ℕ, jj (a + (k : ZMod d)) = jj a + Fin.ofNat n k
  | 0 => by
    have : Fin.ofNat n 0 = 0 := by apply Fin.ext; simp [Fin.ofNat]
    simp [this]
  | k + 1 => by
    have e : a + ((k + 1 : ℕ) : ZMod d) = (a + (k : ZMod d)) + 1 := by push_cast; ring
    rw [e, h, jj_add jj h a k, ofNat_succ, add_assoc]

theorem afBound_of_upFLaw (Y : FBChart C V OE dd) (p : PairData Y d I)
    (vm : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] (hv : vm.Integers R)
    [Fact ¬IsUnit ((V.l : ℕ) : R)] [IsAdicComplete (Ideal.span {((V.l : ℕ) : R)}) R] [IsLocalRing R] [Algebra ℤ_[V.l] R]
    (hMM : ∀ x : R, V.MM (algebraMap R C x) → x ∈ maximalIdeal R)
    (T : Type) [CommRing T] (FT : Fin dd → PS T 2 dd)
    (actT : OE → Fin dd → PS T 1 dd) (hL : UpFLaw V.l T OE dd FT actT)
    (iota : T →+* R) (hloc : IsLocalHom iota)
    (emR : Fin 2 → ZMod d → OE →+* R) (hem : ∀ g a x, algebraMap R C (emR g a x) = p.em g a x)
    (hPl : ∀ g, PlaceIn V.l OE R d (emR g))
    (hEig : EigIn p R (fun a i => MvPowerSeries.map iota (actT a i)) emR) :
    AFBound Y p vm R (fun i => MvPowerSeries.map iota (FT i)) := by
  have := Y.algClosed
  intro g a _
  obtain ⟨w, iN, t, jj, hj1, hjt, hbas⟩ := hPl g
  obtain ⟨r, W, hW, hWe⟩ := hEig
  have hinj : Function.Injective (algebraMap R C) := hv.hom_inj
  have hfrob : ∀ (j : Fin w.n) (x : OE), ((t (j + 1) : Emb (O := R) w.e) : OE →+* R) x -
      (((t j : Emb (O := R) w.e) : OE →+* R) x) ^ V.l ∈ maximalIdeal R := by
    intro j x
    obtain ⟨a', rfl⟩ := jj.surjective j
    rw [← hj1, hjt, hjt]
    apply hMM
    rw [map_sub, map_pow, hem, hem]
    exact p.em_frob g a' x
  obtain ⟨xs, hAF, hle⟩ := hL C vm R hv iota hloc w t hbas hfrob r W hW (jj a)
  obtain ⟨e, he⟩ := hWe g a
  have hconj : ∀ b, (emR g b).comp ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom = emR (1 - g) b := by
    intro b
    ext x
    apply hinj
    show algebraMap R C (emR g b (star x)) = _
    rw [hem, hem]
    fin_cases g
    · exact (p.em_conj b x).symm
    · show p.em 1 b (star x) = p.em 0 b x
      rw [p.em_conj, star_star]
  have hrk : ∀ b, r (emR (1 - g) b) = rk p (1 - g) b := by
    intro b
    obtain ⟨e', -⟩ := hWe (1 - g) b
    have := Fintype.card_congr e'
    rw [Fintype.card_fin, Fintype.card_subtype] at this
    exact this
  refine ⟨r (emR g a), e, W (emR g a), xs, he, ?_, ?_⟩
  · rw [hjt a] at hAF
    exact hAF
  · have hs : S4.frobSum V.l (rk p (1 - g)) a = ∑' n : ℕ, ((V.l : ℝ) ^ (-((n : ℝ) + 1))) *
          (r (((t (jj a + Fin.ofNat w.n (n + 1)) : Emb (O := R) w.e) : OE →+* R).comp
            ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom) : ℝ) := by
      unfold S4.frobSum
      refine tsum_congr fun n => ?_
      rw [← jj_add jj hj1 a (n + 1), hjt, hconj, hrk, rpow_neg_succ V.l_prime.pos]
    rw [hs]
    rw [map_natCast] at hle
    exact hle

theorem upChar_of_upFLaw (Y : FBChart C V OE dd) (p : PairData Y d I) (hr : (Y.raw p).RankHyp)
    (Hc : ∀ g, (Y.raw p).CartHyp V g)
    (vm : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] (hT : ValTie V vm) (hv : vm.Integers R)
    (h0 : 0 < (vm (V.l : C) : ℝ)) (h1 : (vm (V.l : C) : ℝ) < 1)
    [Fact ¬IsUnit ((V.l : ℕ) : R)] [IsAdicComplete (Ideal.span {((V.l : ℕ) : R)}) R] [IsLocalRing R] [Algebra ℤ_[V.l] R]
    (hMM : ∀ x : R, V.MM (algebraMap R C x) → x ∈ maximalIdeal R)
    (T : Type) [CommRing T] (FT : Fin dd → PS T 2 dd)
    (actT : OE → Fin dd → PS T 1 dd) (hL : UpFLaw V.l T OE dd FT actT)
    (iota : T →+* R) (hloc : IsLocalHom iota)
    (hF : ∀ i, Y.B.G.F i = toC (MvPowerSeries.map iota (FT i)))
    (emR : Fin 2 → ZMod d → OE →+* R) (hem : ∀ g a x, algebraMap R C (emR g a x) = p.em g a x)
    (hPl : ∀ g, PlaceIn V.l OE R d (emR g))
    (hEig : EigIn p R (fun a i => MvPowerSeries.map iota (actT a i)) emR) : UPCharSt Y p Hc := by
  refine upChar_of_afBound Y p hr Hc vm R hT hv h0 h1 (fun i => MvPowerSeries.map iota (FT i)) hF ?_
    (afBound_of_upFLaw Y p vm R hv hMM T FT actT hL iota hloc emR hem hPl hEig)
  intro i
  apply hv.hom_inj
  have := Y.B.G.const i
  rw [hF i, MvPowerSeries.constantCoeff_map] at this
  rw [this, map_zero]

theorem upChar_of_upF [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE]
    (hUp : UpFSt V.l) (Y : FBChart C V OE dd) (p : PairData Y d I) (hr : (Y.raw p).RankHyp)
    (Hc : ∀ g, (Y.raw p).CartHyp V g)
    (vm : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] (hT : ValTie V vm) (hv : vm.Integers R)
    (h0 : 0 < (vm (V.l : C) : ℝ)) (h1 : (vm (V.l : C) : ℝ) < 1)
    [Fact ¬IsUnit ((V.l : ℕ) : R)] [IsAdicComplete (Ideal.span {((V.l : ℕ) : R)}) R] [IsLocalRing R] [Algebra ℤ_[V.l] R]
    (hMM : ∀ x : R, V.MM (algebraMap R C x) → x ∈ maximalIdeal R)
    (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [IsNoetherianRing T] [CharZero T]
    [IsAdicComplete (maximalIdeal T) T] (hlT : ¬ IsUnit ((V.l : ℕ) : T))
    (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G] (aG : OE → (G ⟶ G)) (FT : Fin dd → PS T 2 dd)
    (actT : OE → Fin dd → PS T 1 dd) (hG : GeoJ T G OE aG dd FT actT)
    (iota : T →+* R) (hloc : IsLocalHom iota)
    (hF : ∀ i, Y.B.G.F i = toC (MvPowerSeries.map iota (FT i)))
    (hdisc : ¬ ((V.l : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE)))
    (emR : Fin 2 → ZMod d → OE →+* R) (hem : ∀ g a x, algebraMap R C (emR g a x) = p.em g a x)
    (hPl : ∀ g, PlaceIn V.l OE R d (emR g))
    (hEig : EigIn p R (fun a i => MvPowerSeries.map iota (actT a i)) emR) : UPCharSt Y p Hc :=
  upChar_of_upFLaw Y p hr Hc vm R hT hv h0 h1 hMM T FT actT
    (upFLaw_of_geoJ hUp Y.l_odd T hlT G aG FT actT hG hdisc) iota hloc hF emR hem hPl hEig

end Inst

end UpFBr

end Formalism.L2.FormalSeriesBounds
