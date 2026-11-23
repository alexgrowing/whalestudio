import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardAbelianVarietyTorsionSepClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTateIsoOfPeriods
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HTTate

theorem torsion_card (A : Over (Sp ℂ)) [GrpObj A] (hA : IsAbelianScheme A) {n : ℕ} (hn : 0 < n) {K : Type} [Field K]
    [IsSepClosed K] (t : Sp K ⟶ Sp ℂ) (z : Sp K) :
    Finite {x : Over.mk t ⟶ A // x ^ n = 1} ∧
      Nat.card {x : Over.mk t ⟶ A // x ^ n = 1} = (torsion A n).hom.finrank (t z) := by
  have hu : IsUnit (n : Γ(Sp ℂ, ⊤)) := GlobalTheory.SepClosedTorsion.isUnit_natCast_top (by exact_mod_cast hn.ne')
  obtain ⟨-, hfin, het⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A (hG := hA) hu
  let e2 : (Over.mk t ⟶ torsion A n) ≃ {x : Sp K ⟶ (torsion A n).left // x ≫ (torsion A n).hom = t} :=
    { toFun := fun y => ⟨y.left, Over.w y⟩
      invFun := fun x => Over.homMk x.1 x.2
      left_inv := fun y => Over.OverMorphism.ext rfl
      right_inv := fun x => rfl }
  let e : {x : Over.mk t ⟶ A // x ^ n = 1} ≃ {x : Sp K ⟶ (torsion A n).left // x ≫ (torsion A n).hom = t} :=
    (GlobalTheory.TorsionUnram.torsionEquiv A n (Over.mk t)).symm.trans e2
  obtain ⟨h1, h2⟩ := GlobalTheory.FinEt.card_points_eq_finrank (torsion A n).hom t z
  exact ⟨Finite.of_equiv _ e.symm, (Nat.card_congr e).trans h2⟩

def toC {k : Type} [Field k] (j : ℂ →+* k) : Over.mk (spMap j) ⟶ Over.mk (𝟙 (Sp ℂ)) :=
  Over.homMk (spMap j) (Category.comp_id _)

theorem toC_left {k : Type} [Field k] (j : ℂ →+* k) : (toC j).left = spMap j := rfl

theorem pre_injective {k : Type} [Field k] (j : ℂ →+* k) (A : Over (Sp ℂ)) [GrpObj A] :
    Function.Injective (preHom (G := A) (toC j)) := by
  intro x y h
  have hf : Flat (spMap j) := by
    rw [Flat.SpecMap_iff]
    letI := j.toAlgebra
    exact (inferInstance : Module.Flat ℂ k)
  have hs : Surjective (spMap j) := ⟨fun q => ⟨default, Subsingleton.elim (α := PrimeSpectrum ℂ) _ _⟩⟩
  have : Epi (spMap j) := Flat.epi_of_flat_of_surjective _
  apply Over.OverMorphism.ext
  have h' := congrArg (fun z => z.left) h
  simp only [preHom, MonoidHom.mk'_apply, Over.comp_left, toC_left] at h'
  exact (cancel_epi (spMap j)).1 h'

theorem pre_onto {k : Type} [Field k] [IsAlgClosed k] (j : ℂ →+* k) (A : Over (Sp ℂ)) [GrpObj A]
    (hA : IsAbelianScheme A) {n : ℕ} (hn : 0 < n) (x : Over.mk (spMap j) ⟶ A) (hx : x ^ n = 1) :
    ∃ y : Over.mk (𝟙 (Sp ℂ)) ⟶ A, y ^ n = 1 ∧ preHom (toC j) y = x := by
  obtain ⟨z⟩ : Nonempty (Sp k) := inferInstance
  obtain ⟨f₁, c₁⟩ := torsion_card A hA hn (spMap j) z
  obtain ⟨f₀, c₀⟩ := torsion_card A hA hn (𝟙 (Sp ℂ)) (spMap j z)
  let F : {x : Over.mk (𝟙 (Sp ℂ)) ⟶ A // x ^ n = 1} → {x : Over.mk (spMap j) ⟶ A // x ^ n = 1} :=
    fun y => ⟨preHom (toC j) y.1, by rw [← map_pow, y.2, map_one]⟩
  have hF : Function.Injective F := fun y y' h => Subtype.ext (pre_injective j A (congrArg Subtype.val h))
  obtain ⟨y, hy⟩ := (hF.bijective_of_nat_card_le (by rw [c₀, c₁]; rfl)).2 ⟨x, hx⟩
  exact ⟨y.1, y.2, congrArg Subtype.val hy⟩

theorem unitOn_pull {k : Type} [Field k] (j : ℂ →+* k) (c : ℂˣ) :
    Units.map (toC j).left.appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map j.toMonoidHom c) := by
  rw [toC_left]
  apply Units.ext
  exact (congrArg (fun q => q.hom (c : ℂ)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j))).symm

theorem one_comp_hom {S : Scheme.{0}} {T G H : Over S} [GrpObj G] [GrpObj H] (φ : G ⟶ H) [IsMonHom φ] :
    (1 : T ⟶ G) ≫ φ = 1 := by
  rw [Hom.one_def, Category.assoc, IsMonHom.one_hom, ← Hom.one_def]

end GlobalTheory.HTTate

namespace GlobalTheory.UPel.HT

open Classical in

theorem exists_tateIsoO_of_period : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (N : ℕ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (act : OActN D.O A) (L : LB A.left) (D' : PLat D.O D.inv) t (Q : D'.La →+ (Fin D.g → ℂ)) (e : (Fin D.g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (eta : D.La → (𝟙_ (Over (Sp ℂ)) ⟶ A)), 0 < N → N.Coprime p → IsAbelianScheme A → L.IsLB → Genus p N D.plat D' t → IsPeriod D' ρ Q → (∀ z w, e (z + w) = e z * e w) → Function.Surjective e → (∀ z, e z = 1 ↔ z ∈ Q.range) → (∀ a z, e (ρ a *ᵥ z) = e z ≫ act.act a) → (∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) → Out.WeilIs A L k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) → (∀ a, toUnit _ ≫ eta a = e ((N : ℂ)⁻¹ • Q (t a))) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp ℂ), ∃ I : TateIsoO D k (Over.mk x ⟶ A) (fun c g => g ≫ act.act c) (fun n g g' z => Out.WeilIs A L n g g' (unitOn z)), ∀ y, toUnit _ ≫ eta y = I.ev N y := by
  intro p _ D N ρ A _ _ act L D' t Q e eta hN hNp hA hL hG hP hadd hsurj hker hact hW heta k _ _ x
  obtain ⟨f, ν, rfl, htow, hgen⟩ := hG
  obtain ⟨j, rfl⟩ : ∃ j : ℂ →+* k, spMap j = x := ⟨(Spec.preimage x).hom, by simp [spMap]⟩
  have hGF : Out.GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  let π := preHom (G := A) (GlobalTheory.HTTate.toC j)
  have hπ : Function.Injective π := GlobalTheory.HTTate.pre_injective j A
  let e' : Multiplicative (Fin D.g → ℂ) →* (Over.mk (𝟙 (Sp ℂ)) ⟶ A) :=
    MonoidHom.mk' (fun z => e z.toAdd) fun z w => hadd _ _
  have hpow : ∀ (n : ℕ) z, e z ^ n = e (n • z) := fun n z => (map_pow e' (Multiplicative.ofAdd z) n).symm
  have hsm : ∀ n : ℕ, 0 < n → ∀ z : Fin D.g → ℂ, n • (n : ℂ)⁻¹ • z = z := fun n hn z => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn.ne'), one_smul]
  have hsm' : ∀ n : ℕ, 0 < n → ∀ z : Fin D.g → ℂ, (n : ℂ)⁻¹ • n • z = z := fun n hn z => by
    rw [smul_comm, hsm n hn]
  have hshift : ∀ n : ℕ, 0 < n → ∀ a c : D'.La, e ((n : ℂ)⁻¹ • Q (a + n • c)) = e ((n : ℂ)⁻¹ • Q a) := by
    intro n hn a c
    rw [map_add, smul_add, hadd, map_nsmul, hsm' n hn, (hker _).2 ⟨c, rfl⟩, _root_.mul_one]
  let ev : ℕ → D.La → (Over.mk (spMap j) ⟶ A) := fun n a =>
    if 0 < n ∧ n.Coprime p then π (e ((n : ℂ)⁻¹ • Q (f n a))) else 1
  have hev : ∀ n, 0 < n → n.Coprime p → ∀ a, ev n a = π (e ((n : ℂ)⁻¹ • Q (f n a))) :=
    fun n hn hc a => if_pos ⟨hn, hc⟩
  have hev' : ∀ n, ¬ (0 < n ∧ n.Coprime p) → ∀ a, ev n a = 1 := fun n h a => if_neg h
  refine ⟨{ ζ := fun n => Units.map j.toMonoidHom (GlobalTheory.PeriodTate.rt n (ν n))
            ζ_prim := fun n hn hc => (GlobalTheory.PeriodTate.rt_prim hn (hgen n hn hc).1).map_of_injective
              (Units.map_injective j.injective)
            ζ_pow := fun n m hn hm hc => by
              rw [← map_pow, GlobalTheory.PeriodTate.rt_pow hm, GlobalTheory.PeriodTate.rt_congr hn (htow n m hn hm hc).1]
            ev := ev
            add := fun n a b => ?_
            lin := fun n c a => ?_
            ker := fun n hn hc a => ?_
            onto := fun n hn hc q => ?_
            tower := fun n m hn hm hc a => ?_
            isom := fun n hn hc a b => ?_ }, fun y => ?_⟩
  · by_cases h : 0 < n ∧ n.Coprime p
    · have hf : f n (a + b) = f n a + f n b := (f n).map_add a b
      rw [hev n h.1 h.2, hev n h.1 h.2, hev n h.1 h.2, hf, map_add, smul_add, hadd, map_mul]
    · rw [hev' n h, hev' n h, hev' n h, _root_.mul_one]
  · by_cases h : 0 < n ∧ n.Coprime p
    · rw [hev n h.1 h.2, hev n h.1 h.2]
      obtain ⟨d, hd⟩ := (hgen n h.1 h.2).2.1 c a
      replace hd : f n (c • a) = c • f n a + n • d := hd
      show π _ = π _ ≫ _
      rw [hd, hshift n h.1, show π (e ((n : ℂ)⁻¹ • Q (f n a))) ≫ act.act c =
        π (e ((n : ℂ)⁻¹ • Q (f n a)) ≫ act.act c) from Category.assoc _ _ _, ← hact, hP.1, Matrix.mulVec_smul]
    · rw [hev' n h, hev' n h]
      haveI := act.hom c
      exact (GlobalTheory.HTTate.one_comp_hom (act.act c)).symm
  · rw [hev n hn hc, map_eq_one_iff π hπ, hker]
    have hk : (∃ e, f n a = n • e) ↔ ∃ e : D.La, a = n • e := (hgen n hn hc).2.2.1 a
    rw [← hk]
    constructor
    · rintro ⟨c, hc'⟩
      exact ⟨c, hP.2.1 (by rw [map_nsmul, hc', hsm n hn])⟩
    · rintro ⟨c, hc'⟩
      exact ⟨c, by rw [hc', map_nsmul, hsm' n hn]⟩
  · constructor
    · intro hq
      obtain ⟨y, hy, rfl⟩ := GlobalTheory.HTTate.pre_onto j A hA hn q hq
      obtain ⟨z, rfl⟩ := hsurj y
      rw [hpow, hker] at hy
      obtain ⟨a', ha'⟩ := hy
      obtain ⟨a, c, rfl⟩ := (hgen n hn hc).2.2.2.1 a'
      refine ⟨a, (hev n hn hc a).trans (congrArg π ?_)⟩
      rw [← hshift n hn _ c, ha', hsm' n hn]
    · rintro ⟨a, rfl⟩
      rw [hev n hn hc, ← map_pow, hpow, hsm n hn, (hker _).2 ⟨_, rfl⟩, map_one]
  · have hn' : n.Coprime p := Nat.Coprime.coprime_dvd_left (Nat.dvd_mul_right n m) hc
    obtain ⟨c, hc'⟩ := (htow n m hn hm hc).2 a
    replace hc' : f (n * m) a = f n a + n • c := hc'
    rw [hev _ (Nat.mul_pos hn hm) hc, hev n hn hn', ← map_pow, hpow, Nat.cast_mul, mul_inv_rev, mul_smul,
      hsm m hm, hc', hshift n hn]
  · show Out.WeilIs A L n (ev n a) (ev n b)
      (unitOn (Units.map j.toMonoidHom (GlobalTheory.PeriodTate.rt n (ν n)) ^ (2 * D.EF a b)))
    have h := GlobalTheory.CommPairing.weilIs_pull hGF hA hL (GlobalTheory.HTTate.toC j)
      (hW n (f n a) (f n b) (GlobalTheory.PeriodTate.rt n _) hn (GlobalTheory.PeriodTate.rt_val _ _))
    have e2 : D.plat.EF a b = 2 * D.EF a b := by
      show ((2 : ℤ) • D.EF) a b = _
      rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]
    have hν : (n : ℤ) ∣ D'.EF (f n a) (f n b) - ν n * (2 * D.EF a b) := by
      rw [← e2]; exact (hgen n hn hc).2.2.2.2 a b
    rw [GlobalTheory.HTTate.unitOn_pull, GlobalTheory.PeriodTate.rt_congr hn hν, GlobalTheory.PeriodTate.rt_mul, map_zpow] at h
    rw [hev n hn hc, hev n hn hc]
    exact h
  · show toUnit _ ≫ eta y = ev N y
    rw [hev N hN hNp]
    show _ = GlobalTheory.HTTate.toC j ≫ e _
    rw [← heta, ← Category.assoc]
    congr 1
end GlobalTheory.UPel.HT
