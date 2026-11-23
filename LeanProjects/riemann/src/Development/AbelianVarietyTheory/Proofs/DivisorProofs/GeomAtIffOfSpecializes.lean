import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaLin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportAlg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenOfSpecializesIff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeomPointsFactorHenselianOfSpecializes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTorsionPointsRestrictBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootsOfUnityMapBijectiveOfHenselian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilIsRootLocal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubeOfExistsRelAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalStrOfTrivTheta
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullGenLBIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.UPel.HT.LevelClopen

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

theorem eSec_diag {A : Over S} [GrpObj A] :
    eSec A ≫ (lift (1 : A ⟶ A) (𝟙 A)).left = eSec A ≫ (lift (𝟙 A) (𝟙 A)).left := by
  simp only [eSec, ← Over.comp_left]
  congr 1
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, lift_fst, Category.comp_id]
    rw [MonObj.comp_one]
    show toUnit _ ≫ η = η
    rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  · simp

theorem exists_cub {b : Base D R} {s : S ⟶ Sp R} (o : Pre b s) :
    ∃ PP : RigLB o.A, PP.L = o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left ∧ Nonempty (CubicalStr o.A PP) := by
  have hL : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB := pull_isLB o.isLB _
  obtain ⟨t, ht⟩ := GlobalTheory.HkFam.cube_of_exists_relAmple o.ab hL o.ample hL
  have hR : Out.Rigidified o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) := by
    obtain ⟨t₁, ht₁⟩ := o.rig₁
    exact ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_pull_pull o.P (lift (1 : o.A ⟶ o.A) (𝟙 o.A)).left (eSec o.A) _
      (eSec o.A) eSec_diag ⟨pullGenLB t₁ (eSec o.A), pullGenLB_isGen ht₁ _⟩
  exact GlobalTheory.Moduli.cubicalStr_of_triv_theta GlobalTheory.abelianSchemeLaws_all.1 S o.A o.ab _ hL hR ⟨t, ht⟩

theorem isUnit_base {b : Base D R} {s : S ⟶ Sp R} (n : ℕ) (hnp : n.Coprime p) : IsUnit (n : Γ(S, ⊤)) := by
  have := ((b.unit n hnp).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).map s.appTop.hom
  simpa using this

theorem geomAt_transport {b : Base D R} {N : ℕ} (hN : 0 < N) (hNp : N.Coprime p) {s : S ⟶ Sp R}
    (o : PreEta b N s) (R' : Type) [CommRing R'] [HenselianLocalRing R']
    [IsAlgClosed (IsLocalRing.ResidueField R')] (t : Sp R' ⟶ S) {k k' : Type} [Field k] [IsAlgClosed k]
    [Field k'] [IsAlgClosed k'] (i : Sp k ⟶ Sp R') (i' : Sp k' ⟶ Sp R') :
    o.GeomAt k (i ≫ t) → o.GeomAt k' (i' ≫ t) := by
  intro hT
  have hA := o.ab
  have hS : ∀ n : ℕ, 0 < n → n.Coprime p → IsUnit (n : Γ(S, ⊤)) :=
    fun n _ hnp => isUnit_base (b := b) (s := s) n hnp
  have hRu : ∀ n : ℕ, 0 < n → n.Coprime p → IsUnit (n : R') := by
    intro n hn hnp
    have := ((hS n hn hnp).map t.appTop.hom).map (Scheme.ΓSpecIso (CommRingCat.of R')).hom.hom
    simpa using this
  obtain ⟨PP, hPP, ⟨cub⟩⟩ := exists_cub o.toPre
  unfold PreEta.GeomAt at hT ⊢
  change ∃ I : TateIsoO D k' (Over.mk (i' ≫ t) ⟶ o.A) _
      (fun n g g' z => Out.WeilIs o.A (o.toPre.P.pull (lift (𝟙 o.toPre.A) (𝟙 o.toPre.A)).left) n g g' (unitOn z)), _
  rw [← hPP]
  change ∃ I : TateIsoO D k (Over.mk (i ≫ t) ⟶ o.A) _
      (fun n g g' z => Out.WeilIs o.A (o.toPre.P.pull (lift (𝟙 o.toPre.A) (𝟙 o.toPre.A)).left) n g g' (unitOn z)), _ at hT
  rw [← hPP] at hT
  obtain ⟨φ, rfl⟩ : ∃ φ : R' →+* k, i = spMap φ := ⟨(Spec.preimage i).hom, by simp [spMap]⟩
  obtain ⟨φ', rfl⟩ : ∃ φ' : R' →+* k', i' = spMap φ' := ⟨(Spec.preimage i').hom, by simp [spMap]⟩
  obtain ⟨I, hI⟩ := hT
  let A := o.A
  let lvR : D.La → (Over.mk t ⟶ A) := fun a => toUnit _ ≫ o.eta a
  let j : Over.mk (spMap φ ≫ t) ⟶ Over.mk t := Over.homMk (spMap φ) rfl
  let j' : Over.mk (spMap φ' ≫ t) ⟶ Over.mk t := Over.homMk (spMap φ') rfl
  have hj : ∀ a, toUnit (Over.mk (spMap φ ≫ t)) ≫ o.eta a = j ≫ lvR a := fun a => by
    simp only [lvR, ← Category.assoc]; congr 1
  have hj' : ∀ a, toUnit (Over.mk (spMap φ' ≫ t)) ≫ o.eta a = j' ≫ lvR a := fun a => by
    simp only [lvR, ← Category.assoc]; congr 1
  let ρ : (Over.mk t ⟶ A) →* (Over.mk (spMap φ ≫ t) ⟶ A) :=
    { toFun := fun g => j ≫ g, map_one' := MonObj.comp_one _, map_mul' := fun g h => MonObj.comp_mul _ _ _ }
  let ρ' : (Over.mk t ⟶ A) →* (Over.mk (spMap φ' ≫ t) ⟶ A) :=
    { toFun := fun g => j' ≫ g, map_one' := MonObj.comp_one _, map_mul' := fun g h => MonObj.comp_mul _ _ _ }
  have hpull : ∀ {K : Type} [Field K] (ψ : R' →+* K) (n : ℕ) (g h : Over.mk t ⟶ A) (u : R'ˣ),
      Out.WeilIs A PP.L (n : ℤ) g h (unitOn u) →
      Out.WeilIs A PP.L (n : ℤ) ((Over.homMk (spMap ψ) rfl : Over.mk (spMap ψ ≫ t) ⟶ Over.mk t) ≫ g)
        ((Over.homMk (spMap ψ) rfl : Over.mk (spMap ψ ≫ t) ⟶ Over.mk t) ≫ h)
        (unitOn (Units.map ψ.toMonoidHom u)) := by
    intro K _ ψ n g h u H
    have H' := GlobalTheory.CommPairing.weilIs_pull GlobalTheory.globalFns_holds hA PP.isLB
      (Over.homMk (spMap ψ) rfl : Over.mk (spMap ψ ≫ t) ⟶ Over.mk t) H
    have e : Units.map (spMap ψ).appTop.hom.toMonoidHom (unitOn u) = unitOn (Units.map ψ.toMonoidHom u) :=
      Units.ext (congrArg (fun q => q.hom (u : R')) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ))).symm
    exact e ▸ H'
  have hetapow : ∀ a, o.eta a ^ N = 1 := by
    intro a
    have : ∀ m : ℕ, o.eta (m • a) = o.eta a ^ m := by
      intro m
      induction m with
      | zero =>
        have h0 := o.eta_add 0 0
        rw [add_zero] at h0
        rw [zero_smul, pow_zero]
        exact left_eq_mul.1 h0 |>.symm ▸ rfl
      | succ m ih => rw [succ_nsmul, o.eta_add, ih, pow_succ]
    rw [← this]; exact o.eta_ker a
  have hpow : ∀ a, lvR a ^ N = 1 := fun a => by
    simp only [lvR]; rw [← MonObj.comp_pow, hetapow, MonObj.comp_one]
  have h1 : ∀ n, 0 < n → n.Coprime p → ∀ g h : Over.mk t ⟶ A, g ^ n = 1 → h ^ n = 1 → ρ g = ρ h → g = h :=
    fun n hn hnp => (GlobalTheory.T.abelian_scheme_torsion_points_restrict_bijective S A hA n hn (hS n hn hnp) R' t k φ).1
  have h2 : ∀ n, 0 < n → n.Coprime p → ∀ x : Over.mk (spMap φ ≫ t) ⟶ A, x ^ n = 1 →
      ∃ g : Over.mk t ⟶ A, g ^ n = 1 ∧ ρ g = x :=
    fun n hn hnp => (GlobalTheory.T.abelian_scheme_torsion_points_restrict_bijective S A hA n hn (hS n hn hnp) R' t k φ).2
  have h3 : ∀ n, 0 < n → n.Coprime p → ∀ g h : Over.mk t ⟶ A, g ^ n = 1 → h ^ n = 1 → ρ' g = ρ' h → g = h :=
    fun n hn hnp => (GlobalTheory.T.abelian_scheme_torsion_points_restrict_bijective S A hA n hn (hS n hn hnp) R' t k' φ').1
  have h4 : ∀ n, 0 < n → n.Coprime p → ∀ x : Over.mk (spMap φ' ≫ t) ⟶ A, x ^ n = 1 →
      ∃ g : Over.mk t ⟶ A, g ^ n = 1 ∧ ρ' g = x :=
    fun n hn hnp => (GlobalTheory.T.abelian_scheme_torsion_points_restrict_bijective S A hA n hn (hS n hn hnp) R' t k' φ').2
  have h5 := fun n (hn : 0 < n) (hnp : n.Coprime p) =>
    (GlobalTheory.rootsOfUnity_map_bijective_of_henselian R' k φ n hn (hRu n hn hnp))
  have h6 := fun n (hn : 0 < n) (hnp : n.Coprime p) =>
    (GlobalTheory.rootsOfUnity_map_bijective_of_henselian R' k' φ' n hn (hRu n hn hnp))
  have h7 : ∀ (c : D.O) (g h : Over.mk t ⟶ A), (g * h) ≫ o.act.act c = (g ≫ o.act.act c) * (h ≫ o.act.act c) := by
    intro c g h
    haveI := o.act.hom c
    exact MonObj.mul_comp _ _ _
  have h8 : ∀ c, (1 : Over.mk (spMap φ' ≫ t) ⟶ A) ≫ o.act.act c = 1 := by
    intro c
    haveI := o.act.hom c
    exact MonObj.one_comp _
  have h9 : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ g h : Over.mk t ⟶ A, g ^ n = 1 → h ^ n = 1 →
      ∃ u : R'ˣ, u ^ n = 1 ∧ Out.WeilIs A PP.L (n : ℤ) (ρ g) (ρ h) (unitOn (Units.map φ.toMonoidHom u)) ∧
        Out.WeilIs A PP.L (n : ℤ) (ρ' g) (ρ' h) (unitOn (Units.map φ'.toMonoidHom u)) := by
    intro n hn hnp g h hg hh
    obtain ⟨u, hu, H⟩ := GlobalTheory.WeilRootLocal.exists_weilIs_root_local S A hA PP cub R' t n g h hg hh
    exact ⟨u, hu, hpull φ n g h u H, hpull φ' n g h u H⟩
  have h10 : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ (x y : Over.mk (spMap φ ≫ t) ⟶ A) (c c' : kˣ),
      Out.WeilIs A PP.L (n : ℤ) x y (unitOn c) → Out.WeilIs A PP.L (n : ℤ) x y (unitOn c') → c = c' :=
    fun n _ _ x y c c' h h' => GlobalTheory.weilIs_unique_fieldPoint S A PP.L PP.isLB k (spMap φ ≫ t) n x y c c' h h'
  obtain ⟨I', hI'⟩ := GlobalTheory.UPel.HT.TateTransportO.transport_alg D (R := R') (k := k) (k' := k')
    (QR := Over.mk t ⟶ A) (Q := Over.mk (spMap φ ≫ t) ⟶ A) (Q' := Over.mk (spMap φ' ≫ t) ⟶ A)
    (fun a b => mul_comm a b) (fun c g => g ≫ o.act.act c) (fun c g => g ≫ o.act.act c)
    (fun c g => g ≫ o.act.act c)
    (fun n g g' c => Out.WeilIs A PP.L n g g' (unitOn c)) (fun n g g' c => Out.WeilIs A PP.L n g g' (unitOn c))
    ρ ρ' (Units.map φ.toMonoidHom) (Units.map φ'.toMonoidHom)
    h1 h2 h3 h4 (fun n hn hnp => (h5 n hn hnp).1) (fun n hn hnp => (h5 n hn hnp).2)
    (fun n hn hnp => (h6 n hn hnp).1)
    h7 (fun c g => (Category.assoc j g (o.act.act c)).symm) (fun c g => (Category.assoc j' g (o.act.act c)).symm)
    h8 h9 h10 I
  exact ⟨I', fun a => (hj' a).trans (hI' N hN hNp a (lvR a) (hpow a) ((hj a).symm.trans (hI a)))⟩

theorem geomAt_iff_of_specializes {b : Base D R} {N : ℕ} (hN : 0 < N) (hNp : N.Coprime p) {s : S ⟶ Sp R}
    (o : PreEta b N s) {k k' : Type} [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k']
    (x : Sp k ⟶ S) (x' : Sp k' ⟶ S) (u : Sp k) (u' : Sp k') (h : x'.base u' ⤳ x.base u) :
    o.GeomAt k x ↔ o.GeomAt k' x' := by
  obtain ⟨R', _, _, _, r, i, i', rfl, rfl⟩ := GlobalTheory.geomPoints_factor_henselian_of_specializes x x' u u' h
  exact ⟨geomAt_transport hN hNp o R' r i i', geomAt_transport hN hNp o R' r i' i⟩

end GlobalTheory.UPel.HT.LevelClopen

namespace GlobalTheory.UPel.HT

open LevelClopen

theorem PreEta.exists_clopen_geomAt : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R)
    (o : PreEta b N s), ∃ U : S.Opens, IsClosed (U : Set S) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k]
    (x : Sp k ⟶ S), (Set.range x.base ⊆ (U : Set S) ↔ o.GeomAt k x) := by
  intro p _ D R _ b N hN3 hNp S _ s o
  have hN : 0 < N := by omega
  let U : Set S := {z | ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (x : Sp k ⟶ S),
    z ∈ Set.range x.base ∧ o.GeomAt k x}
  have hclo : IsClopen U := by
    refine GlobalTheory.SpecGenClopen.isClopen_of_specializes_iff S U fun z w hzw => ?_
    constructor
    · rintro ⟨k, _, _, x, ⟨u, hu⟩, hG⟩
      obtain ⟨k', _, _, x', hx'⟩ := GlobalTheory.FinEt.exists_algClosed_point S w
      obtain ⟨u', hu'⟩ : w ∈ Set.range x'.base := by rw [show Set.range x'.base = {w} from hx']; rfl
      refine ⟨k', inferInstance, inferInstance, x', ⟨u', hu'⟩,
        (geomAt_iff_of_specializes hN hNp o x' x u' u ?_).2 hG⟩
      rw [hu, hu']
      exact hzw
    · rintro ⟨k, _, _, x, ⟨u, hu⟩, hG⟩
      obtain ⟨k', _, _, x', hx'⟩ := GlobalTheory.FinEt.exists_algClosed_point S z
      obtain ⟨u', hu'⟩ : z ∈ Set.range x'.base := by rw [show Set.range x'.base = {z} from hx']; rfl
      refine ⟨k', inferInstance, inferInstance, x', ⟨u', hu'⟩,
        (geomAt_iff_of_specializes hN hNp o x x' u u' ?_).1 hG⟩
      rw [hu, hu']
      exact hzw
  refine ⟨⟨U, hclo.isOpen⟩, hclo.isClosed, fun k _ _ x => ⟨fun hx => ?_,
    fun hG z hz => ⟨k, inferInstance, inferInstance, x, hz, hG⟩⟩⟩
  let pt : Sp k := (⊥ : PrimeSpectrum k)
  obtain ⟨k', _, _, x', ⟨u', hu'⟩, hG'⟩ := hx ⟨pt, rfl⟩
  exact (geomAt_iff_of_specializes hN hNp o x x' pt u' (hu' ▸ specializes_rfl)).2 hG'

end GlobalTheory.UPel.HT
