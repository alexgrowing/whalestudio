import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniTrait
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabTors
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyLevelOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelStructureRationalThetaPointSubfield
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaPointDeterminesAndEndDeterminedTorsion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenRelNeZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.LabelRigid

open GlobalTheory.LevelOfPairing

section Abstract

variable {G U : Type} [Group G] [CommGroup U] {W : G → G → U → Prop} {M : ℕ}

theorem eq_of_pairing (cm : ∀ a b : G, Commute a b)
    (hu : ∀ x y : G, x ^ M = 1 → y ^ M = 1 → ∃! c, W x y c)
    (hm : ∀ x x' y c c', W x y c → W x' y c' → W (x * x') y (c * c'))
    (hn : ∀ x : G, x ^ M = 1 → (∀ y, y ^ M = 1 → W x y 1) → x = 1) {a b : G} (ha : a ^ M = 1) (hb : b ^ M = 1)
    (h : ∀ y, y ^ M = 1 → ∃ c, W a y c ∧ W b y c) : a = b := by
  have ha' : a⁻¹ ^ M = 1 := by rw [inv_pow, ha, inv_one]
  refine inv_mul_eq_one.1 (hn _ (by rw [(cm _ _).mul_pow, ha', hb, _root_.mul_one]) fun y hy => ?_)
  obtain ⟨c, h₁, h₂⟩ := h y hy
  obtain ⟨d, hd, -⟩ := hu _ y ha' hy
  have e := hm _ _ _ _ _ hd h₁
  rw [inv_mul_cancel] at e
  exact (hu 1 y (one_pow _) hy).unique e (rel_one hu hm hy) ▸ hm _ _ _ _ _ hd h₂

theorem comb_eq (cm : ∀ a b : G, Commute a b)
    (hu : ∀ x y : G, x ^ M = 1 → y ^ M = 1 → ∃! c, W x y c)
    (hm : ∀ x x' y c c', W x y c → W x' y c' → W (x * x') y (c * c'))
    (hn : ∀ x : G, x ^ M = 1 → (∀ y, y ^ M = 1 → W x y 1) → x = 1) {I : Type} {y₁ y₂ : I → G}
    (t₁ : ∀ p, y₁ p ^ M = 1) (t₂ : ∀ p, y₂ p ^ M = 1) (s₂ : ∀ y, y ^ M = 1 → ∃ p, y₂ p = y)
    (hw : ∀ p q c, W (y₁ p) (y₁ q) c → W (y₂ p) (y₂ q) c) {r : ℕ} (b : Fin r → I) (a : Fin r → ℕ) (p : I)
    (hp : y₁ p = (List.ofFn fun i => y₁ (b i) ^ a i).prod) : y₂ p = (List.ofFn fun i => y₂ (b i) ^ a i).prod := by
  refine eq_of_pairing cm hu hm hn (t₂ p) (prod_pow_eq_one cm _ (fun i => t₂ (b i)) a) fun y hy => ?_
  obtain ⟨q, rfl⟩ := s₂ y hy
  choose c hc using fun i => (hu _ _ (t₁ (b i)) (t₁ q)).exists
  have o₁ := rel_one hu hm (t₁ q)
  have o₂ := rel_one hu hm (t₂ q)
  refine ⟨∏ i, c i ^ a i, hw _ _ _ ?_, rel_prod hm o₂ _ _ fun i => rel_pow hm o₂ (hw _ _ _ (hc i)) _⟩
  rw [hp]
  exact rel_prod hm o₁ _ _ fun i => rel_pow hm o₁ (hc i) _

end Abstract

theorem eq_of_isAlgClosed {K : Type} [Field K] [IsAlgClosed K] [CharZero K] (P : PolAV (Sp K)) {n j m : ℕ}
    (hn : n.Prime) (ho : Odd n) (hm : m = n ^ j * (n ^ 2) ^ 2) (hb : ((n ^ 2) ^ 2) ^ P.g * P.g.factorial < m)
    {I : Type} {y₁ y₂ : I → (baseOver (Sp K) ⟶ P.A)}
    (t₁ : ∀ p, y₁ p ^ (m ^ 2) = 1) (t₂ : ∀ p, y₂ p ^ (m ^ 2) = 1)
    (s₁ : ∀ y, y ^ (m ^ 2) = 1 → ∃ p, y₁ p = y) (s₂ : ∀ y, y ^ (m ^ 2) = 1 → ∃ p, y₂ p = y)
    (hw : ∀ p q c, WeilIs P.A P.L (m ^ 2 : ℕ) (y₁ p) (y₁ q) c → WeilIs P.A P.L (m ^ 2 : ℕ) (y₂ p) (y₂ q) c)
    (hfix : ∀ p, y₁ p ^ n = 1 → y₂ p = y₁ p) {v : I → Γ((baseOver (Sp K)).left, ⊤)}
    (v₁ : IsThetaPt P m y₁ v) (v₂ : IsThetaPt P m y₂ v) (p : I) : y₂ p = y₁ p := by
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  have := P.isAb.comm
  have cm : ∀ a b : baseOver (Sp K) ⟶ P.A, Commute a b := fun a b => _root_.mul_comm a b
  have hm0 : m ^ 2 ≠ 0 := pow_ne_zero _ (by omega)
  have hK : ((m ^ 2 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 hm0
  have : NeZero (m ^ 2) := ⟨hm0⟩
  have : NeZero ((m ^ 2 : ℕ) : K) := ⟨hK⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K (m ^ 2)
  have hζ := hz.isUnit_unit (NeZero.ne _)
  generalize (hz.isUnit (NeZero.ne _)).unit = ζ at hζ
  obtain ⟨lev⟩ := GlobalTheory.nonempty_level_of_isAlgClosed K P (m ^ 2) ζ hK hζ
  obtain ⟨hu, hmul, -⟩ := hL.weil _ P (m ^ 2) (baseOver (Sp K))
  have hnd := hL.weilNondeg K P (m ^ 2) hK
  choose b hb' using fun i => s₁ _ (lev.torsion i)
  have eb : lev.pt = fun i => y₁ (b i) := funext fun i => (hb' i).symm
  have comb : ∀ (a : Fin (2 * P.g) → ℕ) (q : I), y₁ q = linComb lev.pt a → y₂ q = linComb (fun i => y₂ (b i)) a :=
    fun a q h => comb_eq (W := fun a b u => WeilIs P.A P.L (m ^ 2 : ℕ) a b u) cm hu hmul hnd t₁ t₂ s₂ hw b a q
      (by rw [h, eb]; rfl)
  have prim : ∀ {T : Type} [CommRing T] [Nontrivial T] (φ : K →+* T),
      IsPrimitiveRoot (Units.map φ.toMonoidHom ζ) (m ^ 2) := fun φ =>
    hζ.map_of_injective (f := Units.map φ.toMonoidHom) (Units.map_injective φ.injective)
  obtain ⟨lev', hl'⟩ := GlobalTheory.exists_level_of_pairing hL.globalFns hL.weil hL.mulN (Sp K) P (m ^ 2) (unitOn ζ) lev.prim
    (fun F _ s => by
      have : Nontrivial Γ(Spec (CommRingCat.of F), ⊤) :=
        (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
      refine ⟨?_, prim (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)⟩
      rw [← map_natCast (Spec.preimage s).hom]
      exact (map_ne_zero _).2 hK) (fun i => y₂ (b i)) (fun i => t₂ _)
    (fun i k => hw _ _ _ (by rw [hb', hb']; exact lev.pairing i k))
  choose q hq using fun a => s₁ _ (ThetaPtDet.levelPoint_pow lev rfl a)
  have e₁ : (fun a => y₁ (q a)) = GlobalTheory.levelPoint lev rfl := funext hq
  have e₂ : (fun a => y₂ (q a)) = GlobalTheory.levelPoint lev' rfl := funext fun a =>
    (comb _ _ (hq a)).trans (by rw [← hl']; rfl)
  have w₁ := ThetaDescentLevel.isThetaPt_reindex v₁ q
  have w₂ := ThetaDescentLevel.isThetaPt_reindex v₂ q
  rw [e₁] at w₁
  rw [e₂] at w₂
  obtain ⟨φ, ⟨hφ, t, ht⟩, hl⟩ := GlobalTheory.thetaPtDetermines_and_endDeterminedOnTorsion.1 P.g n 2 j _ m hn ho le_rfl rfl hm hb K
    (Nat.cast_ne_zero.2 hn.ne_zero) P P rfl rfl _ lev lev' _ w₁ w₂
  have key : ∀ p, y₁ p ≫ φ.hom = y₂ p := fun p => by
    obtain ⟨d, hd⟩ := lev.span K (𝟙 _) (y₁ p) (t₁ p)
    have hd' : linComb lev.pt (fun i => (d i : ℕ)) = y₁ p :=
      (congrArg (linComb · _) (funext fun i => (Category.id_comp (lev.pt i)).symm)).trans hd
    rw [comb _ _ hd'.symm, ← hd', ThetaPtDet.linComb_comp, ← hl']
    exact congrArg (linComb · _) (funext hl)
  obtain ⟨w, hw'⟩ := LBIso.symm (⟨t, ht⟩ : LBIso _ _)
  have h3 : 3 ≤ n := by
    have := hn.two_le
    obtain ⟨c, rfl⟩ := ho
    omega
  have hid := MatchRigid.aut_eq_id hL P (𝟙 _) h3 (Nat.cast_ne_zero.2 hn.ne_zero) φ w hw' fun x hx => by
    have hd : n ∣ m ^ 2 := by
      rw [hm]
      exact dvd_pow (Dvd.dvd.mul_left (dvd_pow (dvd_pow_self n two_ne_zero) two_ne_zero) _) two_ne_zero
    obtain ⟨c, hc⟩ := hd
    obtain ⟨r, rfl⟩ := s₁ x (by rw [hc, pow_mul]; erw [hx]; exact one_pow _)
    exact (key r).trans (hfix r hx)
  rw [← key, hid, Category.comp_id]

theorem labels_eq : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (n j m : ℕ), n.Prime → Odd n → m = n ^ j * (n ^ 2) ^ 2 → ((n ^ 2) ^ 2) ^ A.g * A.g.factorial < m → ∀ (x₁ x₂ : QkPt D (Kb R) (m ^ 2) → (TFK (R := R) (Kb R) ⟶ A.A)), LabTors D A (m ^ 2) x₁ → LabTors D A (m ^ 2) x₂ → (∀ p, x₁ p ^ n = 1 → x₂ p = x₁ p) → ∀ v : QkPt D (Kb R) (m ^ 2) → Kb R, IsThetaPt A m x₁ (fun p => GlobalTheory.Ex.fnOf (v p)) → IsThetaPt A m x₂ (fun p => GlobalTheory.Ex.fnOf (v p)) → ∀ p, x₂ p = x₁ p := by
  intro R _ _ _ D A n j m hn ho hm hb x₁ x₂ ⟨s₁, t₁, _, _, w₁⟩ ⟨s₂, t₂, _, _, w₂⟩ hfix v v₁ v₂ p
  have hL := GlobalTheory.abelianSchemeLaws_all.1
  have : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R _)
  obtain ⟨P, g, hg, hP, hmul, hs⟩ := hL.polBaseChange _ (Sp (Kb R)) (jFK (R := R) (Kb R)) A
  have hp : IsGrpPullback P.A A.A _ g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = toBase hg.w x), (Over.OverMorphism.ext hy : y₀ = toBase hg.w y), ← hmul]
    rfl⟩
  have hl : LBIso P.L (A.L.pull g) := LBIso.symm hs
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback hp (𝟙 (Sp (Kb R))) (jFK (R := R) (Kb R)) (Category.id_comp _).symm
  have hE : ∀ x, x.left = (e.symm x).left ≫ g := fun x =>
    (congrArg (fun z => z.left) (e.apply_symm_apply x).symm).trans (he _)
  have kW : ∀ (s : Sp (Kb R) ⟶ Sp (FractionRing R)) (_ : s = 𝟙 _ ≫ jFK (R := R) (Kb R))
      (x y : baseOver (Sp (Kb R)) ⟶ P.A) (x₀ y₀ : Over.mk s ⟶ A.A) (c : Γ(Sp (Kb R), ⊤)ˣ),
      x₀.left = x.left ≫ g → y₀.left = y.left ≫ g →
      (WeilIs P.A P.L (m ^ 2 : ℕ) x y c ↔ WeilIs A.A A.L (m ^ 2 : ℕ) x₀ y₀ c) := by
    rintro s rfl x y x₀ y₀ c hx hy
    have := P.isAb.comm
    exact weilIs_grpPullback_of_comm' _ _ _ _ _ g _ _ A.isLB P.isLB hp hl (baseOver _) _ x y x₀ y₀ c hx hy
  have kT : ∀ (s : Sp (Kb R) ⟶ Sp (FractionRing R)) (_ : s = 𝟙 _ ≫ jFK (R := R) (Kb R))
      (x : QkPt D (Kb R) (m ^ 2) → (baseOver (Sp (Kb R)) ⟶ P.A)) (x₀ : QkPt D (Kb R) (m ^ 2) → (Over.mk s ⟶ A.A))
      (u : QkPt D (Kb R) (m ^ 2) → Γ(Sp (Kb R), ⊤)), (∀ i, (x₀ i).left = (x i).left ≫ g) →
      (∀ i, x i ^ m ^ 2 = 1) → IsThetaPt A m x₀ u → IsThetaPt P m x u := by
    rintro s rfl x x₀ u hx ht h
    exact (ThetaPtUp.isThetaPt_iff (T := baseOver (Sp (Kb R))) hp hl hx ht _).2 h
  have tor : ∀ {k : ℕ} (x), x ^ k = 1 → e.symm x ^ k = 1 := fun x h => by rw [← map_pow, h, map_one]
  have tor' : ∀ {k : ℕ} (x), x ^ k = 1 → e x ^ k = 1 := fun x h => by rw [← map_pow, h, map_one]
  refine e.symm.injective (eq_of_isAlgClosed P hn ho hm (by rw [hP]; exact hb) (y₁ := fun p => e.symm (x₁ p))
    (y₂ := fun p => e.symm (x₂ p)) (fun p => tor _ (t₁ p)) (fun p => tor _ (t₂ p))
    (fun y hy => (s₁ _ (tor' y hy)).imp fun q h => (congrArg e.symm h).trans (e.symm_apply_apply y))
    (fun y hy => (s₂ _ (tor' y hy)).imp fun q h => (congrArg e.symm h).trans (e.symm_apply_apply y))
    (fun q q' c h => ?_) (fun q h => congrArg e.symm (hfix q ?_))
    (kT _ (Category.id_comp _).symm _ _ _ (fun i => hE _) (fun i => tor _ (t₁ i)) v₁)
    (kT _ (Category.id_comp _).symm _ _ _ (fun i => hE _) (fun i => tor _ (t₂ i)) v₂) p)
  · obtain ⟨z, rfl⟩ : ∃ z : (Kb R)ˣ, unitOn z = c :=
      ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of (Kb R))).hom.hom.toMonoidHom c, Units.ext
        ((Scheme.ΓSpecIso (CommRingCat.of (Kb R))).commRingCatIsoToRingEquiv.symm_apply_apply c.val)⟩
    exact (kW _ (Category.id_comp _).symm _ _ _ _ _ (hE _) (hE _)).2 ((w₂ _ _ _).1 ((w₁ _ _ _).2
      ((kW _ (Category.id_comp _).symm _ _ _ _ _ (hE _) (hE _)).1 h)))
  · exact (congrArg (· ^ n) (e.apply_symm_apply _).symm).trans (tor' _ h)

end GlobalTheory.Mum.LabelRigid
