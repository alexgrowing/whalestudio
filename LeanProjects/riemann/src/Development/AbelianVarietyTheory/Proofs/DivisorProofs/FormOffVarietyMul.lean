import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeSubAFiniteFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearIsIsoOfIsProperOfFinitePresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeBundleTrivialGeometricFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqrtHeckePointWeilPairingOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BiextensionTrivialOfTranslateDifferenceTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedLineBundleTrivialOfTorsionGeometricFibStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPel.HT.HeckeRootA
open GlobalTheory.UPel.HT.HeckeRoot

variable {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {K : Type} [Field K] {Q : Type} [Group Q]
    {act : D.O → Q → Q} {e : ℕ → Q → Q → Kˣ → Prop}

theorem dvd_pair (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ) (c k n : ℕ) (hk0 : k ≠ 0) (hck : c ∣ k ^ 2)
    (hkn : (k : ℤ) ^ 2 ∣ n) (hsim : ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y)
    (hon : ∀ x, ∃ y z, h n y = k • x + n • z) (x v : D.La) :
    (k : ℤ) ∣ ((k ^ 2 / c : ℕ) : ℤ) * D.EF (h n x) v := by
  obtain ⟨y, z, hyz⟩ := hon v
  have hmZ : ((k ^ 2 / c : ℕ) : ℤ) * c = (k : ℤ) ^ 2 := by exact_mod_cast Nat.div_mul_cancel hck
  have h1 : D.EF (h n x) (h n y) = (k : ℤ) * D.EF (h n x) v + n * D.EF (h n x) z := by
    rw [hyz, map_add, map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul]
  have h2 := hsim x y
  rw [h1] at h2

  have h3 : (k : ℤ) ^ 2 ∣ (k : ℤ) * (((k ^ 2 / c : ℕ) : ℤ) * D.EF (h n x) v) := by
    have e1 : (k : ℤ) * (((k ^ 2 / c : ℕ) : ℤ) * D.EF (h n x) v)
        = ((k ^ 2 / c : ℕ) : ℤ) * ((k : ℤ) * D.EF (h n x) v + n * D.EF (h n x) z - c * u n * D.EF x y)
          - ((k ^ 2 / c : ℕ) : ℤ) * n * D.EF (h n x) z + (k : ℤ) ^ 2 * (u n * D.EF x y) := by
      rw [← hmZ]; ring
    rw [e1]
    refine dvd_add (dvd_sub (Dvd.dvd.mul_left (hkn.trans h2) _) ?_) (dvd_mul_right _ _)
    exact (hkn.trans (dvd_mul_left _ _)).mul_right _
  have hkZ : (k : ℤ) ≠ 0 := by exact_mod_cast hk0
  rw [pow_two] at h3
  exact (mul_dvd_mul_iff_left hkZ).1 h3

end GlobalTheory.UPel.HT.HeckeRootA

namespace GlobalTheory.UPel.HT.HeckeRootA
open GlobalTheory.UPel.HT.HeckeRoot

variable {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {K : Type} [Field K] {Q : Type} [Group Q]
    {act : D.O → Q → Q} {e : ℕ → Q → Q → Kˣ → Prop}

theorem sqrt_hecke_point_weil_orthogonal (I : TateIsoO D K Q act e) (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ)
    (c k N : ℕ) (hk : k.Coprime p) (hN : 0 < N) (hNp : N.Coprime p) (hck : c ∣ k ^ 2)
    (hcomp : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p →
      (∀ x, ∃ z, h (n * m) x = h n x + n • z) ∧ (n : ℤ) ∣ u (n * m) - u n)
    (hsim : ∀ n, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧
      ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y)
    (hon : ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, h n y = k • x + n • z) (x : D.La) :
    ∃ (n : ℕ) (h' : Q), 0 < n ∧ n.Coprime p ∧ h' ^ 2 = I.ev (N * k) (N • h (N * k) x) ∧
      (h' ^ (k ^ 2 / c)) ^ n = 1 ∧ ∀ z : Q, z ^ n = 1 → e n (h' ^ (k ^ 2 / c)) z 1 := by
  have hp : p.Prime := Fact.out
  have hk0 : k ≠ 0 := by
    rintro rfl; exact hp.one_lt.ne' (Nat.coprime_zero_left _ |>.mp hk)
  have hL : 0 < N * k := Nat.mul_pos hN (Nat.pos_of_ne_zero hk0)
  have gen : ∀ M j t : ℕ, 0 < M → k ∣ M → (N * k * M).Coprime p → 2 * j = M + t * (k * M) →
      ∃ (n : ℕ) (h' : Q), 0 < n ∧ n.Coprime p ∧ h' ^ 2 = I.ev (N * k) (N • h (N * k) x) ∧
        (h' ^ (k ^ 2 / c)) ^ n = 1 ∧ ∀ z : Q, z ^ n = 1 → e n (h' ^ (k ^ 2 / c)) z 1 := by
    intro M j t hM hkM hcop hj
    have hn' : 0 < N * k * M := Nat.mul_pos hL hM
    obtain ⟨M', rfl⟩ := hkM
    have hkn : (k : ℤ) ^ 2 ∣ ((N * k * (k * M') : ℕ) : ℤ) := ⟨N * M', by push_cast; ring⟩
    refine ⟨N * k * (k * M'), I.ev (N * k * (k * M')) (j • N • h (N * k * (k * M')) x), hn', hcop, ?_, ?_⟩
    · obtain ⟨z, hz⟩ := (hcomp (N * k) (k * M') hL hM hcop).1 x
      have e1 : 2 • j • N • h (N * k * (k * M')) x
          = (k * M') • (N • h (N * k * (k * M')) x) + (N * k * (k * M')) • (t • h (N * k * (k * M')) x) := by
        simp only [smul_smul, ← add_smul]
        congr 1
        calc 2 * (j * N) = (2 * j) * N := by ring
          _ = _ := by rw [hj]; ring
      rw [← ev_nsmul, e1, I.add, (I.ker _ hn' hcop _).2 ⟨_, rfl⟩, _root_.mul_one, ev_nsmul,
        I.tower (N * k) (k * M') hL hM hcop, hz, smul_add, I.add, smul_comm N (N * k) z,
        (I.ker _ hL (Nat.Coprime.coprime_dvd_left (Dvd.intro _ rfl) hcop) _).2 ⟨_, rfl⟩, _root_.mul_one]
    · rw [← ev_nsmul]
      refine pair_one I _ hn' hcop _ (fun v => ?_)
      obtain ⟨a, ha⟩ := dvd_pair h u c k _ hk0 hck hkn ((hsim _ hn' hcop).2) (hon _ hn' hcop) x v
      have e2 : 2 * D.EF ((k ^ 2 / c) • j • N • h (N * k * (k * M')) x) v
          = (2 * j : ℕ) * N * (((k ^ 2 / c : ℕ) : ℤ) * D.EF (h (N * k * (k * M')) x) v) := by
        simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
        push_cast; ring
      rw [e2, ha, hj]
      exact ⟨(1 + t * k) * a, by push_cast; ring⟩
  by_cases hp2 : p = 2
  · subst hp2
    have hodd : k % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one k with h0 | h0
      · exfalso
        have h2 : 2 ∣ Nat.gcd k 2 := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h0) dvd_rfl
        rw [hk] at h2; omega
      · exact h0
    obtain ⟨r, hr⟩ : ∃ r, k = 2 * r + 1 := ⟨k / 2, by omega⟩
    refine gen k (k * (r + 1)) 1 (Nat.pos_of_ne_zero hk0) dvd_rfl (Nat.Coprime.mul (Nat.Coprime.mul hNp hk) hk) ?_
    rw [hr]; ring
  · have h2p : (2 : ℕ).Coprime p := (Nat.coprime_primes Nat.prime_two hp).2 (fun h0 => hp2 h0.symm)
    refine gen (k * 2) k 0 (by positivity) (dvd_mul_right _ _)
      (Nat.Coprime.mul (Nat.Coprime.mul hNp hk) (Nat.Coprime.mul hk h2p)) ?_
    ring

end GlobalTheory.UPel.HT.HeckeRootA

namespace GlobalTheory.UPel.HT.HeckeAd.KerPol
open GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.HeckeAd

theorem fibre_triv (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R)
    (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ) (c k N : ℕ) (hk : k.Coprime p) (hN : 3 ≤ N) (hNp : N.Coprime p)
    (hck : c ∣ k ^ 2)
    (hcomp : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p →
      (∀ x, ∃ z, h (n * m) x = h n x + n • z) ∧ (n : ℤ) ∣ u (n * m) - u n)
    (hsim : ∀ n, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧
      ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y)
    (hon : ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, h n y = k • x + n • z)
    (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s) (g : 𝟙_ (Over S) ⟶ o.A)
    (hg : g ∈ heckeSubA o (h (N * k)) N) (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S) :
    ∃ t : (((GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).pull (lift (toUnit o.A ≫ g) (𝟙 o.A)).left).pull
      (pullback.fst o.A.hom y)).Gen, t.IsGen := by
  obtain ⟨x, rfl⟩ := hg
  obtain ⟨β, hβ⟩ : ∃ β : R →+* K, y ≫ s = spMap β :=
    ⟨(Spec.preimage (y ≫ s)).hom, by simp [spMap]⟩
  obtain ⟨I, hI⟩ := o.geom K y β hβ
  obtain ⟨n, h', hn0, hnp, hsq, hpow, hW⟩ :=
    GlobalTheory.UPel.HT.HeckeRootA.sqrt_hecke_point_weil_orthogonal I h u c k N hk (by omega) hNp hck hcomp hsim hon x
  have hnK : (n : K) ≠ 0 := by
    have := (b.unit n hnp).map β
    rw [map_natCast] at this
    exact this.ne_zero
  have htr := GlobalTheory.HeckeFibre.transl_triv o.A o.ab _ (pull_isLB o.isLB _)
    (GlobalTheory.HeckeFibre.rigidified_diag o.A o.P o.isLB o.rig₁) K y n hnK
    (h' ^ (k ^ 2 / c)) hpow (fun z hz => by
      have w := hW z hz
      have e1 : unitOn (1 : Kˣ) = 1 := map_one _
      rw [e1] at w
      exact w)
  exact GlobalTheory.PicBilin.triv_pow_of_translDiff o.A o.ab o.P o.isLB o.rig₁ o.rig₂ o.symm (Over.mk y)
    (GlobalTheory.HeckeFibre.pic_field_eq_zero K) (o.eta (N • h (N * k) x)) h' (k ^ 2 / c) (by rw [hsq, hI]) htr

end GlobalTheory.UPel.HT.HeckeAd.KerPol

section Main
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField

namespace GlobalTheory.UPel.HT.HeckeAd.KerPol

theorem hecke_sections_triv : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → c ∣ k ^ 2 → (∀ n, 0 < n → n.Coprime p → ∀ (a : D.O) (x : D.La), ∃ z, h n (a • x) = a • h n x + n • z) → (∀ n m, 0 < n → 0 < m → (n * m).Coprime p → (∀ x, ∃ z, h (n * m) x = h n x + n • z) ∧ (n : ℤ) ∣ u (n * m) - u n) → (∀ n, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧ ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y) → (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, h n y = k • x + n • z) → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ g ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o (h (N * k)) N, (∃ t : ((GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).pull (lift (toUnit o.A ≫ g) (𝟙 o.A)).left).Gen, t.IsGen) ∧ (∃ t : ((GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).pull (lift (𝟙 o.A) (toUnit o.A ≫ g)).left).Gen, t.IsGen) := by
  intro p _ D R _ b h u c k N hc hk hN hNp hck hlin hcomp hsim hon S s o g hg
  have hfib := fibre_triv p D R b h u c k N hk hN hNp hck hcomp hsim hon S s o g hg
  have hP := o.isLB
  have clsPow : ∀ {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (n : ℕ) (h' : (GlobalTheory.UPel.HT.Hecke.lbPow L n).IsLB),
      GlobalTheory.CechPic.cls (GlobalTheory.UPel.HT.Hecke.lbPow L n) h' = n • GlobalTheory.CechPic.cls L hL := by
    intro X L hL n h'
    unfold GlobalTheory.UPel.HT.Hecke.lbPow at h' ⊢
    rw [GlobalTheory.CechPic.cls_linComb hL]
    simp [GlobalTheory.CechPic.pull_id]
  have hQ : (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).IsLB := LB.isLB_linComb hP _ _
  have hadd := (GlobalTheory.AbDual.additive_of_cube GlobalTheory.CubeTop.cubeTheorem o.ab o.ab hP o.rig₁ o.rig₂).1
  have evcCls : ∀ {M : LB (o.A ⊗ o.A).left} (hM : M.IsLB) {Y : Over S} (a t : Y ⟶ o.A),
      GlobalTheory.AbDual.evc hM a t = GlobalTheory.CechPic.pull (lift a t).left (GlobalTheory.CechPic.cls M hM) := by
    intro M hM Y a t
    rw [← GlobalTheory.AbDual.cls_ev hM a t (pull_isLB hM _), GlobalTheory.CechPic.cls_pull hM]
  have evcQ : ∀ {Y : Over S} (a t : Y ⟶ o.A),
      GlobalTheory.AbDual.evc hQ a t = (k ^ 2 / c) • GlobalTheory.AbDual.evc hP a t := by
    intro Y a t
    rw [evcCls hQ, evcCls hP, clsPow hP _ hQ, map_nsmul]
  have hpow : ∀ (a : o.A ⟶ o.A) (n : ℕ),
      GlobalTheory.AbDual.evc hP (a ^ n) (𝟙 o.A) = n • GlobalTheory.AbDual.evc hP a (𝟙 o.A) := by
    intro a n
    induction n with
    | zero => rw [pow_zero, zero_smul]; exact GlobalTheory.AbDual.IsAdditive.evc_one hP hadd _
    | succ n ih => rw [pow_succ, (GlobalTheory.AbDual.isAdditive_iff hP).1 hadd, ih, succ_nsmul]
  set th : o.A ⟶ o.A := toUnit o.A ≫ g with hth
  have hk1 : th ^ k = 1 := by
    rw [hth, ← MonObj.comp_pow, GlobalTheory.UPel.HT.HeckeAd.pow_eq_one_of_mem o (h (N * k)) g hg, MonObj.comp_one]
  have htors : k • GlobalTheory.AbDual.evc hP th (𝟙 o.A) = 0 := by
    rw [← hpow, hk1]; exact GlobalTheory.AbDual.IsAdditive.evc_one hP hadd _
  have hQth : GlobalTheory.AbDual.evc hQ th (𝟙 o.A) = 0 := by
    have hM : (GlobalTheory.AbDual.ev (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) th (𝟙 o.A)).IsLB := pull_isLB hQ _
    have hunit : IsUnit ((k : Γ(S, ⊤))) := by
      have hR := b.unit k hk
      have e := hR.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
      have e2 := e.map (s.appTop.hom)
      simpa using e2
    have hrig : ∃ t : ((GlobalTheory.AbDual.ev (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) th (𝟙 o.A)).pull
        (1 : 𝟙_ (Over S) ⟶ o.A).left).Gen, t.IsGen := by
      rw [← GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hM _), GlobalTheory.CechPic.cls_pull hM, GlobalTheory.AbDual.cls_ev hQ,
        GlobalTheory.AbDual.pull_evc, evcQ, Category.comp_id, GlobalTheory.AbDual.evc_one_right hP o.rig₂, smul_zero]
    have hpowM : ∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow (GlobalTheory.AbDual.ev (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) th (𝟙 o.A)) k).Gen, t.IsGen := by
      have hMk : (GlobalTheory.UPel.HT.Hecke.lbPow (GlobalTheory.AbDual.ev (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) th (𝟙 o.A)) k).IsLB :=
        LB.isLB_linComb hM _ _
      refine (GlobalTheory.CechPic.cls_eq_zero_iff hMk).1 ?_
      rw [clsPow hM k hMk, GlobalTheory.AbDual.cls_ev hQ, evcQ,
        smul_comm, htors, smul_zero]
    obtain ⟨t, ht⟩ := GlobalTheory.T.rigidified_lineBundle_trivial_of_torsion_geometricFibres S o.A o.ab _ hM hrig k hunit hpowM hfib
    exact (GlobalTheory.AbDual.triv_ev_iff hQ _ _).1 ⟨t, ht⟩
  have hsw : GlobalTheory.CechPic.cls o.P hP = GlobalTheory.CechPic.cls (GlobalTheory.AbDual.swap o.P) (pull_isLB hP _) :=
    (GlobalTheory.CechPic.cls_eq_iff _ _).2 o.symm
  refine ⟨(GlobalTheory.AbDual.triv_ev_iff hQ _ _).2 hQth, (GlobalTheory.AbDual.triv_ev_iff hQ _ _).2 ?_⟩
  rw [evcQ, evcCls hP, hsw, ← evcCls (pull_isLB hP _), GlobalTheory.AbDual.evc_swap hP, ← evcQ]
  exact hQth

end GlobalTheory.UPel.HT.HeckeAd.KerPol
end Main
