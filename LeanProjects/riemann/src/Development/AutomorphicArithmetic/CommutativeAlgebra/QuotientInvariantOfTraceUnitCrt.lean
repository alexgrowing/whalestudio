import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

private theorem isIntAf_one' {p : ℕ} [Fact p.Prime] : IsIntAf (1 : AfP p) := fun v => by
  rw [map_one]; exact one_mem _

private theorem inAf_mem' {p : ℕ} [Fact p.Prime] {D : Datum p} (y : D.La) : inAf D y ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, y, isIntAf_one', rfl⟩

set_option maxHeartbeats 200000 in
theorem UpperTheory.quotient_invariant_of_trace_unit_crt :
    NumEx → QComp → QIso → ClsEx → TrEta → TrUnit → CongCRT → BaseInv := by
  intro hNumEx hQComp hQIso hClsEx hTrEta hTrUnit hCRT p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hLev N' N t c a hN't hNum C' C u hu W
  have hNpos : 0 < (N : ℕ) := by have := N.2.1; omega
  have hN'pos : 0 < (N' : ℕ) := by have := N'.2.1; omega
  have hNum' := (hNumEx p D E gb w q r 𝔴 𝔫 S (N : ℕ) hNpos).2 c a t hNum
  obtain ⟨hNc, hGen⟩ := hNum
  obtain ⟨-, hGen'⟩ := hNum'
  rw [← hN't] at hGen'
  have hN'c : (N' : ℕ) = S.N₀ * (c * t) := by rw [hN't, hNc, _root_.mul_assoc]
  have h3 : 3 ≤ S.N₀ := S.std.three
  have hcq : S.N₀.Coprime q := S.std.cop
  have hu1 := ((hLev u).mp hu).1
  have hIu : Integ L u := integ_of_mem hu1
  have hCRTu := hCRT p D G L q r S.N₀ S.𝔞 hcq S.upow u hIu
  have hC := hCRTu.1.mp (by have h1 := ((hLev u).mp hu).2; rwa [S.lev] at h1)
  have hEta : ∀ y : D.La, (T.M N').univ.eta ((c * t) • y) ≫ W.ψ = W.o.eta (c • y) := by
    intro y
    obtain ⟨v, hv, ev⟩ := hC.1 _ (inAf_mem' y)
    exact hTrEta p D G L E gb u _ _ N' N (T.M N').univ W.o W.ψ W.trans S.N₀ (c * t) c hN'c hNc y y ⟨v, hv, ev⟩
  obtain ⟨hIso, hLB⟩ := hTrUnit p D G L E gb u _ _ N' N (T.M N').univ W.o W.ψ W.trans hu1
  obtain ⟨qC, hqC⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N).univ S.Y.univ S.Y.univ C.j (𝟙 _)).2.2.2
    _ _ W.o W.π W.φ C.m
  obtain ⟨n', hn'⟩ := hQIso q _ _ _ _ _ _ _ _ c (c * t) _ _ _ _ (T.M N').univ W.o S.Y.univ _ W.ψ hIso W.trans.1
    W.trans.2.1 hLB hEta qC
  have hov : (W.π ≫ C.j) ≫ S.Y.s = (T.M N').s ≫ spMap (algebraMap (Ow w) E) := by
    rw [Category.assoc, C.ov, reassoc_of% W.ov]
  have hlv : ∀ y : D.La, ((T.M N').univ.eta ((algebraMap (𝓞 D.F) D.O) (↑t * a) • y)).left ≫ n'.φ =
      (W.π ≫ C.j) ≫ (S.Y.lv y).left := by
    intro y
    have hsm : (algebraMap (𝓞 D.F) D.O (↑t * a)) • y = t • ((algebraMap (𝓞 D.F) D.O) a • y) := by
      rw [map_mul, map_natCast, mul_smul, Nat.cast_smul_eq_nsmul]
    obtain ⟨v₂, hv₂, e₂⟩ := (hCRTu.2 a N hNpos N.2.2 hGen).mp hC.2 y
    have hTE := hTrEta p D G L E gb u _ _ N' N (T.M N').univ W.o W.ψ W.trans N t 1 hN't
      (_root_.mul_one _).symm _ _ ⟨v₂, hv₂, e₂⟩
    rw [one_smul] at hTE
    rw [hsm, hn', hqC, ← Category.assoc, ← Over.comp_left, hTE, ← Category.assoc]
    erw [W.φ.eta]
    rw [Category.assoc, C.lv, Category.assoc]
  obtain ⟨-, huq⟩ := hClsEx q _ _ _ S.b gb _ S.mat _ _ _ _ _ hN'c hN'pos h3 hcq hGen' S.Y _ _ (T.M N').univ
  obtain ⟨hj, hm⟩ := huq ⟨W.π ≫ C.j, hov, n', hlv⟩ C'
  refine ⟨hj, ?_⟩
  calc Over.Hom.left W.ψ ≫ W.φ.φ ≫ C.m.φ = n'.φ := by rw [hn', hqC]
    _ = C'.m.φ := hm
