import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialField
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfSurjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusAbelianQuotientPDivisibleSmoothGroupStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FrobGPowAndClosedSubgroup
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FrobGSplitTorusPow
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PullPowOfFix
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AmpleCubPullAndPullPow
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionPullbackPowerLocusLeStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsImage
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionAbelianVarietyLeConstMulPowStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolyNormSqRootsStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.FrobTorsion

theorem card_torsion_le_mul {A B : Type} [CommGroup A] [CommGroup B] (f : A →* B) (n : ℕ)
    [Finite {x : A // f x = 1 ∧ x ^ n = 1}] [Finite {y : B // y ^ n = 1}] :
    Finite {x : A // x ^ n = 1} ∧
      Nat.card {x : A // x ^ n = 1} ≤ Nat.card {x : A // f x = 1 ∧ x ^ n = 1} * Nat.card {y : B // y ^ n = 1} := by
  classical
  let c : B → A := fun b => if h : ∃ a : {x : A // x ^ n = 1}, f a = b then (h.choose : A) else 1
  have hc : ∀ x : {x : A // x ^ n = 1}, (c (f x)) ^ n = 1 ∧ f (c (f x)) = f x := by
    intro x
    have h : ∃ a : {x : A // x ^ n = 1}, f a = f x := ⟨x, rfl⟩
    simp only [c, dif_pos h]
    exact ⟨h.choose.2, h.choose_spec⟩
  let Φ : {x : A // x ^ n = 1} → {x : A // f x = 1 ∧ x ^ n = 1} × {y : B // y ^ n = 1} := fun x =>
    (⟨x * (c (f x))⁻¹, by
        refine ⟨?_, ?_⟩
        · rw [map_mul, map_inv, (hc x).2, mul_inv_cancel]
        · rw [mul_pow, inv_pow, x.2, (hc x).1]
          simp⟩,
     ⟨f x, by rw [← map_pow, x.2, map_one]⟩)
  have hΦ : Function.Injective Φ := by
    intro x y hxy
    simp only [Φ, Prod.mk.injEq, Subtype.mk.injEq] at hxy
    obtain ⟨h1, h2⟩ := hxy
    rw [h2] at h1
    exact Subtype.ext (mul_right_cancel h1)
  have : Finite {x : A // x ^ n = 1} := Finite.of_injective Φ hΦ
  refine ⟨inferInstance, ?_⟩
  have := Nat.card_le_card_of_injective Φ hΦ
  rwa [Nat.card_prod] at this

variable {S : Scheme.{0}}

noncomputable def onPts {G H : Over S} [GrpObj G] [GrpObj H] (φ : G ⟶ H) [IsMonHom φ] (Z : Over S) :
    (Z ⟶ G) →* (Z ⟶ H) :=
  MonoidHom.mk' (fun x => x ≫ φ) fun x y => MonObj.mul_comp x y φ

theorem pow_comp' {G H Z : Over S} [GrpObj G] [GrpObj H] (φ : G ⟶ H) [IsMonHom φ] (x : Z ⟶ G) (n : ℕ) :
    (x ^ n) ≫ φ = (x ≫ φ) ^ n := MonObj.pow_comp x n φ

private theorem list_prod_comp_degeneration {S : Scheme.{0}} {Z G H : Over S} [GrpObj G] [GrpObj H] (φ : G ⟶ H) [IsMonHom φ]
    (l : List (Z ⟶ G)) : l.prod ≫ φ = (l.map (· ≫ φ)).prod := by
  induction l with
  | nil => simp [MonObj.one_comp]
  | cons a l ih => rw [List.prod_cons, MonObj.mul_comp, ih, List.map_cons, List.prod_cons]

theorem polyPt_comp {G H Z : Over S} [GrpObj G] [GrpObj H] (φ : G ⟶ H) [IsMonHom φ] (E : End G) (F : End H)
    (h : (show G ⟶ G from E) ≫ φ = φ ≫ (show H ⟶ H from F)) (P : Polynomial ℤ) (x : Z ⟶ G) :
    polyPt E P x ≫ φ = polyPt F P (x ≫ φ) := by
  unfold polyPt
  rw [list_prod_comp_degeneration, List.map_map]
  congr 1
  apply List.map_congr_left
  intro n _
  simp only [Function.comp_apply]
  rw [GrpObj.zpow_comp, Category.assoc, GlobalTheory.SS.FrobSub.pow_comm_hom φ F E h n]
  simp only [Category.assoc]

theorem pullPow_pull {X Y : Scheme.{0}} (ν : Y ⟶ X) {F : X ⟶ X} {E : Y ⟶ Y} (h : E ≫ ν = ν ≫ F) {L : LB X} {Q : ℤ}
    (hL : PullPow F L Q) : PullPow E (L.pull ν) Q := by
  obtain ⟨t, ht⟩ := hL
  have hc : ∀ k : Fin 2, ν ≫ (![F, 𝟙 X] : Fin 2 → (X ⟶ X)) k = ((![E, 𝟙 Y] : Fin 2 → (Y ⟶ Y)) k) ≫ ν := by
    intro k
    fin_cases k
    · simp [h]
    · simp
  have hle : ∀ (j : Fin 2 → PUnit.{1} → L.ι) (y : Y), y ∈ (L.pull ν).wchart (![E, 𝟙 Y] : Fin 2 → (Y ⟶ Y)) j →
      ν y ∈ L.wchart (![F, 𝟙 X] : Fin 2 → (X ⟶ X)) (fun k => j k PUnit.unit) := by
    intro j y hy
    refine Set.mem_iInter.2 fun k => ?_
    have h2 : ν ((![E, 𝟙 Y] : Fin 2 → (Y ⟶ Y)) k y) ∈ L.U (j k PUnit.unit) := mem_pull.1 (Set.mem_iInter.1 hy k)
    have h3 := congrArg (fun m : Y ⟶ X => m y) (hc k)
    simp only at h3
    change (ν ≫ (![F, 𝟙 X] : Fin 2 → (X ⟶ X)) k) y ∈ L.U (j k PUnit.unit)
    rw [h3]
    exact h2
  let a : ChartPull (LB.LinComb (L.pull ν) (![E, 𝟙 Y] : Fin 2 → (Y ⟶ Y)) ![1, -Q])
      (LB.LinComb L (![F, 𝟙 X] : Fin 2 → (X ⟶ X)) ![1, -Q]) ν :=
    { idx := fun j k => j k PUnit.unit
      le := fun j y hy => hle j y hy
      g := fun y j j' hj hj' => by
        refine (gm_linComb (L.pull ν) _ _ (𝟙 Y) y j j' hj hj').trans
          (Eq.trans ?_ (gm_linComb L _ _ ν y _ _ (hle j y hj) (hle j' y hj')).symm)
        refine Finset.prod_congr rfl fun k _ => ?_
        have m1 : (𝟙 Y ≫ (![E, 𝟙 Y] : Fin 2 → (Y ⟶ Y)) k) y ∈ (L.pull ν).U (j k) := Set.mem_iInter.1 hj k
        have m2 : (𝟙 Y ≫ (![E, 𝟙 Y] : Fin 2 → (Y ⟶ Y)) k) y ∈ (L.pull ν).U (j' k) := Set.mem_iInter.1 hj' k
        rw [gm_pull_g L ν _ y (j k) (j' k) m1 m2, Category.id_comp, ← hc k] }
  obtain ⟨u, hu⟩ := gen_chartPull a t ht
  exact ⟨u, hu⟩

private theorem isMonHom_mul_degeneration {S : Scheme.{0}} {M G : Over S} [MonObj M] [GrpObj G] [IsCommMonObj G]
    (f g : M ⟶ G) [IsMonHom f] [IsMonHom g] : IsMonHom (f * g) := by
  rw [Hom.mul_def]
  infer_instance

theorem isMonHom_id_pow (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ) : IsMonHom ((𝟙 G) ^ n : G ⟶ G) := by
  induction n with
  | zero =>
    rw [pow_zero, Hom.one_def]
    infer_instance
  | succ n ih =>
    rw [pow_succ]
    exact isMonHom_mul_degeneration _ _

theorem norm_lt_of_normSq {β : ℂ} {Q : ℕ} (hQ : 2 ≤ Q) (h : Complex.normSq β = Q) : ‖β‖ < Q := by
  have h1 : ‖β‖ ^ 2 = (Q : ℝ) := by
    rw [← Complex.normSq_eq_norm_sq, h]
  have hQ' : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have h0 : 0 ≤ ‖β‖ := norm_nonneg β
  nlinarith

private theorem comp_mul_inv_pow_eq_one_iff {S : Scheme.{0}} {N Z : Over S} [GrpObj N] [IsCommMonObj N] (E : N ⟶ N) (Q : ℕ)
    (x : Z ⟶ N) : x ≫ (E * ((𝟙 N) ^ Q)⁻¹) = 1 ↔ x ≫ E = x ^ Q := by
  rw [MonObj.comp_mul, GrpObj.comp_inv, MonObj.comp_pow, Category.comp_id, mul_inv_eq_one]

private theorem inv_mul_mul_mul_eq_mul {S : Scheme.{0}} {N : Over S} [GrpObj N] [IsCommMonObj N] (E : N ⟶ N) [IsMonHom E] (Q : ℕ) :
    E ≫ (E * ((𝟙 N) ^ Q)⁻¹) = (E * ((𝟙 N) ^ Q)⁻¹) ≫ E := by
  rw [MonObj.comp_mul, GrpObj.comp_inv, MonObj.comp_pow, Category.comp_id, MonObj.mul_comp, GrpObj.inv_comp,
    MonObj.pow_comp, Category.id_comp]

theorem core (k : Type) [Field k] [IsAlgClosed k] (N : Over (Sp k)) [GrpObj N] (hN : SmConn N)
    (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Sp k)) [GrpObj B]
    (i : splitTorus (Sp k) X ⟶ N) (q : N ⟶ B) (hq : IsQuot i q) (hB : IsAbelianScheme B)
    (L : LB N.left) (hL : AmpleCub N L) (E : N ⟶ N) [IsMonHom E] (Q : ℕ) (hQ : 2 ≤ Q)
    (hE : PullPow E.left L Q) (hi : i ≫ E = i ^ Q) (a : ℕ) (ha : SmoothOfRelativeDimension a B.hom) :
    ∃ (a' C : ℕ) (P : Polynomial ℤ), a' ≤ a ∧ (∀ β : ℂ, Polynomial.aeval β P = 0 → ‖β‖ < Q) ∧
      (∀ n : ℕ, (n : k) ≠ 0 → (Finite {x : 𝟙_ (Over (Sp k)) ⟶ N // x ^ n = 1} ∧
        Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ N // x ^ n = 1} ≤ C * n ^ (Module.finrank ℤ X + 2 * a')) ∧
        Finite {x : 𝟙_ (Over (Sp k)) ⟶ N // x ≫ E = x ^ Q ∧ x ^ n = 1} ∧
        Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ N // x ≫ E = x ^ Q ∧ x ^ n = 1} ≤ C * n ^ Module.finrank ℤ X) ∧
      ∀ y : 𝟙_ (Over (Sp k)) ⟶ N, polyPt (show End N from E) P y ≫ E = polyPt (show End N from E) P y ^ Q := by
  have : IsCommMonObj N := hN.1
  obtain ⟨hi_hom, hq_hom, hq_flat, hq_surj, hq_aff, hq_pb, _⟩ := id hq
  have := hi_hom
  have := hq_hom
  have := hq_flat
  have := hq_surj
  have := hq_aff
  have : IsMonHom ((𝟙 N) ^ Q) := isMonHom_id_pow N Q
  have hRhom : IsMonHom (E * ((𝟙 N) ^ Q)⁻¹) := isMonHom_mul_degeneration _ _
  have hiq : i ≫ q = 1 := hq_pb.w
  have hiR : i ≫ (E * ((𝟙 N) ^ Q)⁻¹) = toUnit _ ≫ η[N] := by
    rw [(comp_mul_inv_pow_eq_one_iff E Q i).2 hi]
    rfl
  obtain ⟨ψ, hψ, hqψ⟩ := GlobalTheory.FlatQuotient.exists_desc q i (E * ((𝟙 N) ^ Q)⁻¹) hq_pb hiR
  have := hψ
  have hiEq : i ≫ (E ≫ q) = toUnit _ ≫ η[B] := by
    rw [← Category.assoc, hi, MonObj.pow_comp, hiq, one_pow]
    rfl
  obtain ⟨EB, _, hqEB⟩ := GlobalTheory.FlatQuotient.exists_desc q i (E ≫ q) hq_pb hiEq
  have hepi : Epi q := GlobalTheory.FlatQuotient.epi_of_flat_surjective q
  have hψE : EB ≫ ψ = ψ ≫ E := by
    apply hepi.left_cancellation
    rw [← Category.assoc, hqEB, Category.assoc, hqψ, inv_mul_mul_mul_eq_mul, ← Category.assoc, hqψ]
  obtain ⟨B', _, ν, π, hB', hν, hνci, hπν, hstab, hdim⟩ :=
    GlobalTheory.AbelianImage.exists_image k N hN B hB ψ hψ
  have := hν
  have := hνci
  obtain ⟨F', hF', hF'ν⟩ := hstab E inferInstance (fun x => ⟨x ≫ EB, by
    simp only [Category.assoc, hψE]⟩)
  have := hF'
  obtain ⟨a', ha'le, ha'⟩ := hdim a ha
  have hL' : AmpleCub B' (L.pull ν.left) :=
    (GlobalTheory.SS.AmpSub.ampleCub_pull_and_pullPow (Sp k) N L hL).1 B' ν hν hνci
  have hpp : PullPow F'.left (L.pull ν.left) Q :=
    pullPow_pull ν.left (by rw [← Over.comp_left, hF'ν, Over.comp_left]) hE
  obtain ⟨P, _, hProots, hPkill⟩ := GlobalTheory.T.exists_poly_normSq_roots' k B' hB' (L.pull ν.left) hL' F' Q hF' hpp
  obtain ⟨C2, hC2⟩ := GlobalTheory.T.card_torsion_pullbackPowerLocus_le k N hN X B i q hq hB L hL E Q hQ inferInstance hE hi
  obtain ⟨C3, hC3⟩ := GlobalTheory.T.card_torsion_abelianVariety_le_const_mul_pow k B' hB' (L.pull ν.left) hL' a' ha'
  have hmono : Mono ν := by
    have : Mono ν.left := inferInstance
    exact (Over.forget _).mono_of_mono_map this
  have : IsMonHom π := by
    have : IsMonHom (π ≫ ν) := by rw [hπν]; infer_instance
    exact GlobalTheory.AbelianImage.isMonHom_of_comp_mono π ν
  have : IsCommMonObj B' := GlobalTheory.AbelianImage.isCommMonObj_of_mono ν
  have hker : ∀ x : 𝟙_ (Over (Sp k)) ⟶ N, x ≫ q ≫ π = 1 → x ≫ E = x ^ Q := by
    intro x hx
    rw [← comp_mul_inv_pow_eq_one_iff, ← hqψ, ← hπν, ← Category.assoc q, ← Category.assoc, hx, MonObj.one_comp]
  refine ⟨a', C2 * (C3 + 1), P, ha'le, fun β hβ => norm_lt_of_normSq hQ (hProots β hβ), ?_, ?_⟩
  · intro n hn
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · exact absurd (by rw [h, Nat.cast_zero]) hn
      · exact h
    obtain ⟨hfin2, hcard2⟩ := hC2 n hn1
    obtain ⟨hfin3, hcard3⟩ := hC3 n hn
    letI : CommGroup (𝟙_ (Over (Sp k)) ⟶ N) := Hom.commGroup
    letI : CommGroup (𝟙_ (Over (Sp k)) ⟶ B') := Hom.commGroup
    let f : (𝟙_ (Over (Sp k)) ⟶ N) →* (𝟙_ (Over (Sp k)) ⟶ B') :=
      { toFun := fun x => x ≫ q ≫ π
        map_one' := MonObj.one_comp _
        map_mul' := fun x y => MonObj.mul_comp x y _ }
    let emb : {x : 𝟙_ (Over (Sp k)) ⟶ N // f x = 1 ∧ x ^ n = 1} →
        {x : 𝟙_ (Over (Sp k)) ⟶ N // x ≫ E = x ^ Q ∧ x ^ n = 1} := fun x => ⟨x.1, hker x.1 x.2.1, x.2.2⟩
    have hemb : Function.Injective emb := by
      intro x y h
      have h' := congrArg Subtype.val h
      exact Subtype.ext h'
    have : Finite {x : 𝟙_ (Over (Sp k)) ⟶ N // f x = 1 ∧ x ^ n = 1} := Finite.of_injective emb hemb
    obtain ⟨hfin, hcard⟩ := card_torsion_le_mul f n
    have hk := Nat.card_le_card_of_injective emb hemb
    refine ⟨⟨hfin, ?_⟩, hfin2, ?_⟩
    · calc Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ N // x ^ n = 1}
          ≤ Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ N // f x = 1 ∧ x ^ n = 1} *
              Nat.card {y : 𝟙_ (Over (Sp k)) ⟶ B' // y ^ n = 1} := hcard
        _ ≤ (C2 * n ^ Module.finrank ℤ X) * (C3 * n ^ (2 * a')) := Nat.mul_le_mul (hk.trans hcard2) hcard3
        _ ≤ C2 * (C3 + 1) * n ^ (Module.finrank ℤ X + 2 * a') := by
          rw [pow_add]
          have : C3 ≤ C3 + 1 := Nat.le_succ C3
          calc C2 * n ^ Module.finrank ℤ X * (C3 * n ^ (2 * a'))
              = C2 * C3 * (n ^ Module.finrank ℤ X * n ^ (2 * a')) := by ring
            _ ≤ C2 * (C3 + 1) * (n ^ Module.finrank ℤ X * n ^ (2 * a')) := by gcongr
    · calc Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ N // x ≫ E = x ^ Q ∧ x ^ n = 1}
          ≤ C2 * n ^ Module.finrank ℤ X := hcard2
        _ ≤ C2 * (C3 + 1) * n ^ Module.finrank ℤ X := by
          gcongr
          exact Nat.le_mul_of_pos_right C2 (Nat.succ_pos C3)
  · intro y
    rw [← comp_mul_inv_pow_eq_one_iff, polyPt_comp (E * ((𝟙 N) ^ Q)⁻¹) E E (inv_mul_mul_mul_eq_mul E Q) P y, ← hqψ, ← hπν,
      show y ≫ q ≫ π ≫ ν = ((y ≫ q) ≫ π) ≫ ν by simp only [Category.assoc],
      ← polyPt_comp ν F' E hF'ν P, hPkill, MonObj.one_comp]

private theorem isClosedImmersion_of_isPullback_unit {k : Type} [Field k] {T N B : Over (Sp k)} [GrpObj B] [IsSeparated B.hom]
    (i : T ⟶ N) (q : N ⟶ B) (h : IsPullback i (toUnit T) q η[B]) : IsClosedImmersion i.left := by
  have hη : IsClosedImmersion (η[B]).left := by
    have : IsClosedImmersion ((η[B]).left ≫ B.hom) := by
      rw [Over.w]
      exact (inferInstance : IsClosedImmersion (𝟙 (Sp k)))
    exact IsClosedImmersion.of_comp _ B.hom
  have h' : IsPullback i.left (toUnit T).left q.left (η[B]).left := h.map (Over.forget (Sp k))
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) h'.flip hη

private theorem eq_of_comp_mono_eq {k : Type} [Field k] {N G : Over (Sp k)} [GrpObj N] [GrpObj G] (ν : N ⟶ G) [Mono ν]
    {x y : 𝟙_ (Over (Sp k)) ⟶ N} (h : x ≫ ν = y ≫ ν) : x = y := by
  exact (cancel_mono ν).1 h

end GlobalTheory.SS.FrobTorsion

open GlobalTheory.SS.FrobTorsion in

theorem GlobalTheory.SS.frobenius_on_torsion : ∀ (k : Type) [Field k] [IsAlgClosed k] (p l : ℕ) [Fact p.Prime] [CharP k p], l.Prime → l ≠ p → ∀ (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (g : ℕ), SmoothOfRelativeDimension g G.hom → ∀ (L : LB G.left), AmpleCub G L → ∀ (F : End G) (q : ℕ), 2 ≤ q → FrobG G F q → ∃ (t a m C : ℕ) (P : Polynomial ℤ) (W : Subgroup (𝟙_ (Over (Sp k)) ⟶ G)), 1 ≤ m ∧ (∀ β : ℂ, Polynomial.aeval β P = 0 → ‖β‖ < (q : ℝ) ^ m) ∧ (∀ x ∈ W, x ≫ (show G ⟶ G from F ^ m) = x ^ (q ^ m)) ∧ (∀ n, Finite {x : (𝟙_ (Over (Sp k)) ⟶ G) // x ^ l ^ n = 1} ∧ Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ G) // x ^ l ^ n = 1} ≤ C * l ^ (n * (t + 2 * a)) ∧ Nat.card {x : W // x ^ l ^ n = 1} ≤ C * l ^ (n * t)) ∧ (∀ (x : (𝟙_ (Over (Sp k)) ⟶ G)) n, x ^ l ^ n = 1 → polyPt (F ^ m) P x ∈ W) ∧ (g ≤ t + a → Nonempty (TorusExtension G)) := by
  intro k _ _ p l _ _ hl hlp G _ hG g hg L hL F q hq hF
  have : IsCommMonObj G := hG.1
  letI : CommGroup (𝟙_ (Over (Sp k)) ⟶ G) := Hom.commGroup
  obtain ⟨N, _, ν, hN, hν, hνci, hdiv, hlift, hFlift, hdimN⟩ :=
    GlobalTheory.DivisiblePart.exists_divisiblePart k p G hG
  have := hν
  have := hνci
  have : IsCommMonObj N := hN.1
  letI : CommGroup (𝟙_ (Over (Sp k)) ⟶ N) := Hom.commGroup
  have hFhom : IsMonHom (show G ⟶ G from F) := hF.1
  obtain ⟨F', hF', hF'ν⟩ := hFlift F hF.1
  have := hF'
  have hνmono : Mono ν := by
    have : Mono ν.left := inferInstance
    exact (Over.forget _).mono_of_mono_map this
  let F'e : End N := F'
  obtain ⟨g', hg', hgiso⟩ := hdimN g hg
  obtain ⟨X, _, _, _, B, _, i, qB, hqB, hB, hdimB⟩ := GlobalTheory.T.exists_torus_abelian_quotient_p_divisible_smooth_group k p N hN hdiv
  obtain ⟨a, ha, hga⟩ := hdimB g' hg'
  have hFN : FrobG N F' q :=
    (GlobalTheory.SS.frobG_pow_and_closed_subgroup k G hG F q hF).2 N ν F' hν hνci hF' hF'ν
  obtain ⟨hi_hom, hq_hom, hq_flat, hq_surj, hq_aff, hq_pb, _⟩ := id hqB
  have := hi_hom
  have := hq_hom
  have : IsProper B.hom := hB.proper
  have htriv : i ≫ F' ≫ qB = toUnit _ ≫ η[B] :=
    GlobalTheory.splitTorus_hom_proper_trivial_field k X B (i ≫ F' ≫ qB) inferInstance
  let F'' : splitTorus (Sp k) X ⟶ splitTorus (Sp k) X :=
    hq_pb.lift (i ≫ F') (toUnit _) (by rw [Category.assoc, htriv])
  have hF''i : F'' ≫ i = i ≫ F' := hq_pb.lift_fst _ _ _
  have : Mono η[B] := ⟨fun a b _ => toUnit_unique a b⟩
  have hi_mono : Mono i := hq_pb.mono_fst_of_mono
  have : IsMonHom (F'' ≫ i) := by rw [hF''i]; infer_instance
  have hF''hom : IsMonHom F'' := GlobalTheory.AbelianImage.isMonHom_of_comp_mono F'' i
  have : IsClosedImmersion i.left := isClosedImmersion_of_isPullback_unit i qB hq_pb
  have hFT : FrobG (splitTorus (Sp k) X) F'' q :=
    (GlobalTheory.SS.frobG_pow_and_closed_subgroup k N hN F' q hFN).2 _ i F'' hi_hom inferInstance hF''hom hF''i
  obtain ⟨m1, hm1, hpow1⟩ := GlobalTheory.SS.frobG_splitTorus_pow k X F'' q hFT
  have hLN : AmpleCub N (L.pull ν.left) :=
    (GlobalTheory.SS.AmpSub.ampleCub_pull_and_pullPow (Sp k) G L hL).1 N ν hν hνci
  obtain ⟨m2, hm2, hpow2⟩ := GlobalTheory.SS.FrobLB.frob_pullPow k N hN F' q hFN (L.pull ν.left) hLN.1
  have hM : 1 ≤ m1 * m2 := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hEhom : IsMonHom (show N ⟶ N from F'e ^ (m1 * m2)) := GlobalTheory.SS.FrobSub.isMonHom_pow N F' hF' (m1 * m2)
  have hQ : 2 ≤ q ^ (m1 * m2) := le_trans hq (Nat.le_self_pow (by omega) q)
  have hE : PullPow (show N ⟶ N from F'e ^ (m1 * m2)).left (L.pull ν.left) ((q ^ (m1 * m2) : ℕ) : ℤ) := by
    have h := hpow2 m1
    rw [show m2 * m1 = m1 * m2 from Nat.mul_comm _ _] at h
    rw [Nat.cast_pow]
    exact h
  have hiE : i ≫ (show N ⟶ N from F'e ^ (m1 * m2)) = i ^ (q ^ (m1 * m2)) := by
    rw [← GlobalTheory.SS.FrobSub.pow_comm_hom i F' F'' hF''i (m1 * m2), hpow1 m2, MonObj.pow_comp, Category.id_comp]
  obtain ⟨a', C, P, ha'le, hroots, hbounds, hfix⟩ :=
    core k N hN X B i qB hqB hB (L.pull ν.left) hLN (show N ⟶ N from F'e ^ (m1 * m2)) (q ^ (m1 * m2)) hQ hE hiE a ha
  have hcomm : (show N ⟶ N from F'e ^ (m1 * m2)) ≫ ν = ν ≫ (show G ⟶ G from F ^ (m1 * m2)) :=
    GlobalTheory.SS.FrobSub.pow_comm_hom ν F F' hF'ν (m1 * m2)
  have hFM : IsMonHom (show G ⟶ G from F ^ (m1 * m2)) := GlobalTheory.SS.FrobSub.isMonHom_pow G F hF.1 (m1 * m2)
  let W : Subgroup (𝟙_ (Over (Sp k)) ⟶ G) :=
    { carrier := {x | x ≫ (show G ⟶ G from F ^ (m1 * m2)) = x ^ (q ^ (m1 * m2))}
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [MonObj.mul_comp, hx, hy, mul_pow]
      one_mem' := by
        simp only [Set.mem_setOf_eq]
        rw [MonObj.one_comp, one_pow]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        rw [GrpObj.inv_comp, hx, inv_pow] }
  have hlk : ∀ n : ℕ, ((l ^ n : ℕ) : k) ≠ 0 := by
    intro n h
    rw [Nat.cast_pow] at h
    have h1 : ((l : ℕ) : k) = 0 := pow_eq_zero_iff'.mp h |>.1
    rw [CharP.cast_eq_zero_iff k p] at h1
    exact hlp ((Nat.prime_dvd_prime_iff_eq (Fact.out) hl).mp h1).symm
  have hcop : ∀ n : ℕ, (l ^ n).Coprime p := fun n =>
    Nat.Coprime.pow_left n ((Nat.coprime_primes hl (Fact.out)).2 hlp)
  have hlpos : ∀ n : ℕ, l ^ n ≠ 0 := fun n => pow_ne_zero n hl.ne_zero
  have hlift' : ∀ (x : 𝟙_ (Over (Sp k)) ⟶ G) (n : ℕ), x ^ l ^ n = 1 →
      ∃ y : 𝟙_ (Over (Sp k)) ⟶ N, y ≫ ν = x ∧ y ^ l ^ n = 1 := by
    intro x n hx
    obtain ⟨y, hy⟩ := hlift x (l ^ n) (hcop n) (hlpos n) hx
    refine ⟨y, hy, eq_of_comp_mono_eq ν ?_⟩
    rw [MonObj.pow_comp, hy, hx, MonObj.one_comp]
  refine ⟨Module.finrank ℤ X, a', m1 * m2, C, P, W, hM, ?_, fun x hx => hx, ?_, ?_, ?_⟩
  · intro β hβ
    have := hroots β hβ
    push_cast at this
    exact this
  · intro n
    obtain ⟨⟨hfinN, hcardN⟩, hfinF, hcardF⟩ := hbounds (l ^ n) (hlk n)
    let f1 : {y : 𝟙_ (Over (Sp k)) ⟶ N // y ^ l ^ n = 1} → {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ l ^ n = 1} :=
      fun y => ⟨y.1 ≫ ν, by rw [← MonObj.pow_comp, y.2, MonObj.one_comp]⟩
    have hf1 : Function.Surjective f1 := by
      intro x
      obtain ⟨y, hy, hyn⟩ := hlift' x.1 n x.2
      exact ⟨⟨y, hyn⟩, Subtype.ext hy⟩
    let f2 : {y : 𝟙_ (Over (Sp k)) ⟶ N // y ≫ (show N ⟶ N from F'e ^ (m1 * m2)) = y ^ (q ^ (m1 * m2)) ∧ y ^ l ^ n = 1} →
        {x : W // x ^ l ^ n = 1} :=
      fun y => ⟨⟨y.1 ≫ ν, by
          show (y.1 ≫ ν) ≫ (show G ⟶ G from F ^ (m1 * m2)) = (y.1 ≫ ν) ^ (q ^ (m1 * m2))
          rw [Category.assoc, ← hcomm, ← Category.assoc, y.2.1, MonObj.pow_comp]⟩, by
        apply Subtype.ext
        rw [SubgroupClass.coe_pow]
        show (y.1 ≫ ν) ^ l ^ n = 1
        rw [← MonObj.pow_comp, y.2.2, MonObj.one_comp]⟩
    have hf2 : Function.Surjective f2 := by
      intro x
      have hxn : (x.1 : 𝟙_ (Over (Sp k)) ⟶ G) ^ l ^ n = 1 := by
        rw [← SubgroupClass.coe_pow, x.2]
        rfl
      obtain ⟨y, hy, hyn⟩ := hlift' x.1.1 n hxn
      have hyE : y ≫ (show N ⟶ N from F'e ^ (m1 * m2)) = y ^ (q ^ (m1 * m2)) := by
        apply eq_of_comp_mono_eq ν
        rw [Category.assoc, hcomm, ← Category.assoc, hy, MonObj.pow_comp, hy]
        exact x.1.2
      exact ⟨⟨y, hyE, hyn⟩, Subtype.ext (Subtype.ext hy)⟩
    have : Finite {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ l ^ n = 1} := Finite.of_surjective f1 hf1
    refine ⟨inferInstance, ?_, ?_⟩
    · calc Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ l ^ n = 1}
          ≤ Nat.card {y : 𝟙_ (Over (Sp k)) ⟶ N // y ^ l ^ n = 1} := Nat.card_le_card_of_surjective f1 hf1
        _ ≤ C * (l ^ n) ^ (Module.finrank ℤ X + 2 * a') := hcardN
        _ = C * l ^ (n * (Module.finrank ℤ X + 2 * a')) := by rw [← pow_mul]
    · calc Nat.card {x : W // x ^ l ^ n = 1}
          ≤ Nat.card {y : 𝟙_ (Over (Sp k)) ⟶ N //
              y ≫ (show N ⟶ N from F'e ^ (m1 * m2)) = y ^ (q ^ (m1 * m2)) ∧ y ^ l ^ n = 1} :=
            Nat.card_le_card_of_surjective f2 hf2
        _ ≤ C * (l ^ n) ^ Module.finrank ℤ X := hcardF
        _ = C * l ^ (n * Module.finrank ℤ X) := by rw [← pow_mul]
  · intro x n hx
    obtain ⟨y, hy, _⟩ := hlift' x n hx
    show polyPt (F ^ (m1 * m2)) P x ≫ (show G ⟶ G from F ^ (m1 * m2)) = (polyPt (F ^ (m1 * m2)) P x) ^ (q ^ (m1 * m2))
    rw [← hy, ← polyPt_comp ν (F'e ^ (m1 * m2)) (F ^ (m1 * m2)) hcomm P y, Category.assoc, ← hcomm,
      ← Category.assoc, hfix y, MonObj.pow_comp]
  · intro hle
    have hgg : g ≤ g' := by omega
    have := hgiso hgg
    have : QuasiCompact qB.left := inferInstance
    let T : TorusExtension N :=
      { X := X, B := B, isAbelian := hB, q := qB, q_hom := hq_hom, q_flat := hq_flat,
        q_surjective := hq_surj, q_quasiCompact := inferInstance, i := i, i_hom := hi_hom, isKernel := hq_pb }
    exact ⟨torusExtOfIso (asIso ν) T⟩
