import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPELTripleOfDenseFibres
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilCommutatorPairingTorsionGeometricPoint
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingBirigidifiedTrivialOnAxesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingSwapEqOfSwapInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingDiagonalPullbackEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingPullbackPowerMapLevelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.UPel.HT.Hecke

section GeomAux

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem liftSq_mul {T : Over S} (a b a' b' : T ⟶ A) :
    (lift a b : T ⟶ G2 A) * lift a' b' = lift (a * a') (b * b') := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [MonObj.mul_comp]; simp
  · rw [MonObj.mul_comp]; simp

theorem liftSq_pow {T : Over S} (a b : T ⟶ A) (n : ℕ) :
    (lift a b : T ⟶ G2 A) ^ n = lift (a ^ n) (b ^ n) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [MonObj.pow_comp]; simp
  · rw [MonObj.pow_comp]; simp

end GeomAux

theorem weilIs_heckeSub_geom : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h₁ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ h₂ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (β : R →+* K), x ≫ s = spMap β → ∀ u : Γ((Over.mk x).left, ⊤)ˣ, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (toUnit (Over.mk x) ≫ (lift h₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A)) (toUnit (Over.mk x) ≫ (lift 1 h₂ : 𝟙_ (Over S) ⟶ G2 o.A)) u → u = 1 := by
  intro p _ D R _ b g c k N hc hk hN hNp hEF hg hck S s o h₁ hh₁ h₂ hh₂ K _ _ x β hx u hu
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hA2 : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  have hPL : o.P.IsLB := o.isLB
  obtain ⟨I, hI⟩ := o.geom K x β hx
  obtain ⟨x₁, rfl⟩ := hh₁
  obtain ⟨x₂, rfl⟩ := hh₂
  have hpp : p.Prime := Fact.out
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; exact absurd (Nat.coprime_zero_left p |>.1 hk) hpp.one_lt.ne'
    · exact h
  have hN0 : 0 < N := by omega
  obtain ⟨m, hm⟩ : ∃ m, m = k ^ 2 / c := ⟨_, rfl⟩
  rw [← hm] at hu
  have hmc : m * c = k ^ 2 := by rw [hm]; exact Nat.div_mul_cancel hck
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, zero_mul] at hmc; exact absurd hmc.symm (pow_ne_zero 2 hk0.ne')
    · exact h
  obtain ⟨j, hj0, hjp, hjpar⟩ : ∃ j : ℕ, 0 < j ∧ (j * k ^ 2).Coprime p ∧ (Even j ∨ Odd (j * k ^ 2)) := by
    by_cases h2 : p = 2
    · subst h2
      have hko : Odd k := Nat.coprime_two_right.1 hk
      exact ⟨1, one_pos, by rw [_root_.one_mul]; exact Nat.Coprime.pow_left 2 hk,
        Or.inr (by rw [_root_.one_mul]; exact hko.pow)⟩
    · refine ⟨2, two_pos, Nat.coprime_mul_iff_left.2 ⟨?_, Nat.Coprime.pow_left 2 hk⟩, Or.inl even_two⟩
      exact (Nat.coprime_primes Nat.prime_two hpp).2 (Ne.symm h2)
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, n₀ = j * k ^ 2 := ⟨_, rfl⟩
  rw [← hn₀] at hjp hjpar
  have hn0 : 0 < n₀ := by rw [hn₀]; positivity

  have ev0 : ∀ n, I.ev n 0 = 1 := fun n => by
    have h := I.add n 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  have evs : ∀ n (z : D.La) (r : ℕ), I.ev n (r • z) = I.ev n z ^ r := fun n z r => by
    induction r with
    | zero => rw [zero_smul, pow_zero, ev0]
    | succ r ih => rw [succ_nsmul, I.add, ih, pow_succ]
  have hdown : ∀ z : D.La, toUnit (Over.mk x) ≫ o.eta (N • g z) = I.ev n₀ (g z) ^ (j * k) := fun z => by
    have t1 := I.tower k N hk0 hN0 (Nat.coprime_mul_iff_left.2 ⟨hk, hNp⟩) (g z)
    have e : k * (j * k) = n₀ := by rw [hn₀]; ring
    have t2 := I.tower k (j * k) hk0 (by positivity) (by rw [e]; exact hjp) (g z)
    rw [Nat.mul_comm k N] at t1
    rw [hI, evs, t1, ← t2, e]
  obtain ⟨w, hw⟩ : ∃ w, w = I.ev n₀ (g x₁) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = I.ev n₀ (g x₂) := ⟨_, rfl⟩
  have ha : toUnit (Over.mk x) ≫ (lift (o.eta (N • g x₁)) 1 : 𝟙_ (Over S) ⟶ G2 o.A) =
      lift (w ^ (j * k)) (1 ^ (j * k)) := by
    rw [comp_lift, hdown, ← hw, one_pow, MonObj.comp_one]
  have hb : toUnit (Over.mk x) ≫ (lift 1 (o.eta (N • g x₂)) : 𝟙_ (Over S) ⟶ G2 o.A) =
      lift (1 ^ (j * k)) (y ^ (j * k)) := by
    rw [comp_lift, hdown, ← hy, one_pow, MonObj.comp_one]
  rw [ha, hb] at hu
  have e1 := GlobalTheory.T.commutatorPairing_pullback_powerMap_level S o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) o.P o.ab (pull_isLB hPL _) o.ample hPL
    o.rig₁ o.rig₂ m (j * k) (j * k) 1 (Over.mk x) w 1 1 y u hu

  have hwn : w ^ n₀ = 1 := (I.onto n₀ hn0 hjp w).2 ⟨g x₁, hw.symm⟩
  have hyn : y ^ n₀ = 1 := (I.onto n₀ hn0 hjp y).2 ⟨g x₂, hy.symm⟩
  have hK : ((n₀ : ℕ) : K) ≠ 0 := by
    have := (b.unit n₀ hjp).map β
    rw [map_natCast] at this
    exact this.ne_zero
  have tor : ∀ a a' : Over.mk x ⟶ o.A, a ^ n₀ = 1 → a' ^ n₀ = 1 →
      (lift a a' : Over.mk x ⟶ G2 o.A) ^ n₀ = 1 := fun a a' h h' => by
    rw [liftSq_pow, h, h']
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have one_n : (1 : Over.mk x ⟶ o.A) ^ n₀ = 1 := one_pow _
  have ex : ∀ X Y : Over.mk x ⟶ G2 o.A, X ^ n₀ = 1 → Y ^ n₀ = 1 →
      ∃ e : Γ((Over.mk x).left, ⊤)ˣ, Out.WeilIs (G2 o.A) o.P (n₀ : ℤ) X Y e := fun X Y hX hY =>
    GlobalTheory.WeilGeomPt.exists_weilIs_geomPt S (G2 o.A) o.P hA2 hPL K x n₀ hn0 hK X Y hX hY
  obtain ⟨F, hF⟩ := ex _ _ (tor w 1 hwn one_n) (tor 1 y one_n hyn)
  have hFp : ∀ r : ℕ, Out.WeilIs (G2 o.A) o.P (n₀ : ℤ) (lift (w ^ (r + 1)) 1) (lift 1 y) (F ^ (r + 1)) := by
    intro r
    induction r with
    | zero => simpa using hF
    | succ r ih =>
      have := GlobalTheory.SiegelTypings.weilIs_mul hA2 hPL ih hF
      rwa [liftSq_mul, _root_.mul_one, ← pow_succ, ← pow_succ] at this
  have hjm : j * m = (j * m - 1) + 1 := (Nat.sub_add_cancel (Nat.mul_pos hj0 hm0)).symm
  have hFjm : Out.WeilIs (G2 o.A) o.P (n₀ : ℤ) (lift (w ^ (j * m)) 1) (lift 1 y) (F ^ (j * m)) := by
    rw [hjm]; exact hFp _
  have hl1 : (GlobalTheory.UPel.HT.Hecke.lbPow o.P 1).IsLB := LB.isLB_linComb hPL _ _
  have iso1 : LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P 1) (o.P.pull (Over.Hom.left (𝟙 (G2 o.A)))) := by
    have c1 := GlobalTheory.CechPic.cls_linComb hPL (fun _ : Fin 1 => 𝟙 (G2 o.A).left) (fun _ => (1 : ℤ)) hl1
    have c2 := GlobalTheory.CechPic.cls_pull hPL (Over.Hom.left (𝟙 (G2 o.A))) (pull_isLB hPL _)
    refine (GlobalTheory.CechPic.cls_eq_iff hl1 (pull_isLB hPL _)).1 (c1.trans (Eq.trans ?_ c2.symm))
    simp
  have e2' : Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P 1) (n₀ : ℤ) (lift (w ^ (j * m)) (1 ^ 1))
      (lift (1 ^ (j * m)) (y ^ 1)) (F ^ (j * m)) := by
    rw [one_pow, one_pow, pow_one]
    exact GlobalTheory.PELFamily.weilIs_of_lbIso hG hA2 hl1 hPL iso1 hFjm
  have e2 := GlobalTheory.T.commutatorPairing_pullback_powerMap_level S o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) o.P o.ab (pull_isLB hPL _) o.ample hPL
    o.rig₁ o.rig₂ 1 (j * m) 1 (n₀ : ℤ) (Over.mk x) w 1 1 y _ e2'
  have hlev : (1 : ℤ) * ((m * (j * k) * (j * k) : ℕ) : ℤ) = (n₀ : ℤ) * ((1 * (j * m) * 1 : ℕ) : ℤ) := by
    rw [hn₀]; push_cast; ring

  have hu' : u = F ^ (j * m) := GlobalTheory.CommutatorPairing.weilIs_unique hG hA2 hPL e1 (hlev ▸ e2)

  have hgeo := I.isom n₀ hn0 hjp (g x₁) (g x₂)
  rw [← hw, ← hy] at hgeo
  obtain ⟨c11, h11⟩ := ex (lift w 1) (lift y 1) (tor w 1 hwn one_n) (tor y 1 hyn one_n)
  obtain ⟨c21, h21⟩ := ex (lift 1 w) (lift y 1) (tor 1 w one_n hwn) (tor y 1 hyn one_n)
  obtain ⟨c22, h22⟩ := ex (lift 1 w) (lift 1 y) (tor 1 w one_n hwn) (tor 1 y one_n hyn)
  have hA := GlobalTheory.SiegelTypings.weilIs_mul hA2 hPL h11 h21
  have hB := GlobalTheory.SiegelTypings.weilIs_mul hA2 hPL hF h22
  rw [liftSq_mul, _root_.mul_one, _root_.one_mul] at hA hB
  have hs := GlobalTheory.CommPairing.weilIs_symm hPL (GlobalTheory.SiegelTypings.weilIs_mul hA2 hPL
    (GlobalTheory.CommPairing.weilIs_symm hPL hA) (GlobalTheory.CommPairing.weilIs_symm hPL hB))
  rw [liftSq_mul, _root_.mul_one, _root_.one_mul] at hs
  have hd := GlobalTheory.T.weilPairing_diagonal_pullback_eq S o.A o.P o.ab hPL _ (Over.mk x) w y _ _ hs hgeo
  have e11 := (GlobalTheory.T.weilPairing_birigidified_trivial_on_axes S o.A o.P o.ab hPL o.rig₁ o.rig₂ _ (Over.mk x) w y c11).1 h11
  have e22 := (GlobalTheory.T.weilPairing_birigidified_trivial_on_axes S o.A o.P o.ab hPL o.rig₁ o.rig₂ _ (Over.mk x) w y c22).2 h22
  have e21 := GlobalTheory.T.commutatorPairing_swap_eq_of_swap_invariant S o.A o.P o.ab hPL o.symm _ (Over.mk x) w y c21 F h21 hF
  rw [e11, e22, e21] at hd
  have hF2 : F ^ 2 = unitOn (I.ζ n₀ ^ (2 * ((c : ℤ) * D.EF x₁ x₂))) := by
    rw [← hEF, ← hd]; group

  have hζ : I.ζ n₀ ^ n₀ = 1 := (I.ζ_prim n₀ hn0 hjp).pow_eq_one
  have hz : ∀ z : ℤ, I.ζ n₀ ^ ((n₀ : ℤ) * z) = 1 := fun z => by
    rw [zpow_mul, zpow_natCast, hζ, one_zpow]
  have hmcZ : (m : ℤ) * c = (k : ℤ) ^ 2 := by exact_mod_cast hmc
  have hnZ : (n₀ : ℤ) = j * (k : ℤ) ^ 2 := by rw [hn₀]; push_cast; ring
  have uPow : ∀ (a : Kˣ) (n : ℕ), unitOn (a ^ n) = unitOn a ^ n := fun a n => map_pow (Units.map _) a n
  have uOne : unitOn (1 : Kˣ) = 1 := map_one (Units.map _)
  have hpw : ∀ t : ℕ, F ^ (2 * t) = unitOn (I.ζ n₀ ^ (2 * ((c : ℤ) * D.EF x₁ x₂) * (t : ℤ))) := fun t => by
    rw [pow_mul, hF2, ← uPow, ← zpow_natCast, ← zpow_mul]
  rcases hjpar with ⟨i, hi⟩ | hodd
  · have e : j * m = 2 * (i * m) := by rw [hi]; ring
    rw [hu', e, hpw]
    have ex' : 2 * ((c : ℤ) * D.EF x₁ x₂) * ((i * m : ℕ) : ℤ) = (n₀ : ℤ) * D.EF x₁ x₂ := by
      rw [hnZ, ← hmcZ, hi]; push_cast; ring
    rw [ex', hz, uOne]
  · have h2 : u ^ 2 = 1 := by
      rw [hu', ← pow_mul, Nat.mul_comm, hpw]
      have ex' : 2 * ((c : ℤ) * D.EF x₁ x₂) * ((j * m : ℕ) : ℤ) = (n₀ : ℤ) * (2 * D.EF x₁ x₂) := by
        rw [hnZ, ← hmcZ]; push_cast; ring
      rw [ex', hz, uOne]
    have hFn : F ^ n₀ = 1 := GlobalTheory.SiegelTypings.weil_pow_eq_one hA2 hPL (tor w 1 hwn one_n) hF
    have hn : u ^ n₀ = 1 := by rw [hu', ← pow_mul, Nat.mul_comm, pow_mul, hFn, one_pow]
    have hg := pow_gcd_eq_one.2 ⟨h2, hn⟩
    rwa [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.2 hodd), pow_one] at hg

end GlobalTheory.UPel.HT.Hecke
