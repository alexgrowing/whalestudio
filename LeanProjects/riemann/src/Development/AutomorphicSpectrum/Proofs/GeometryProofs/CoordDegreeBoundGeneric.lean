import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueSemilinearStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelIsBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalAtLocalRingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GradedSandwichDegreeBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeRegularAtLocalPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.FinPhi

theorem flag_coord {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {r : ℕ} (b : Fin r → E)
    (π : Fin r → Module.Dual Ω E) (hπ : ∀ j l, π j (b l) = if j = l then 1 else 0) (n : ℕ) (e : E)
    (he : e ∈ flagStep Ω b n) : e = ∑ l, π l e • b l ∧ ∀ l : Fin r, n ≤ l → π l e = 0 := by
  unfold flagStep at he
  induction he using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    refine ⟨?_, fun l hl => ?_⟩
    · simp [hπ]
    · have : l ≠ k := by
        rintro rfl
        exact absurd hk (by simpa using hl)
      simp [hπ, this]
  | zero => simp
  | add x y _ _ hx hy =>
    refine ⟨?_, fun l hl => by simp [hx.2 l hl, hy.2 l hl]⟩
    simp only [map_add, add_smul, Finset.sum_add_distrib]
    rw [← hx.1, ← hy.1]
  | smul c x _ hx =>
    refine ⟨?_, fun l hl => by simp [hx.2 l hl]⟩
    simp only [map_smul, smul_eq_mul, mul_smul]
    rw [← Finset.smul_sum, ← hx.1]

section Clear

variable {L : Type} [Field L] [NumberField L] {B T : Type} [AddCommGroup B] [Module (𝓞 L) B]
  [AddCommGroup T] [Module L T] [Module (𝓞 L) T] [IsScalarTower (𝓞 L) L T]

theorem dvd_nat (c : 𝓞 L) (hc : c ≠ 0) : ∃ (n : ℕ) (d : 𝓞 L), n ≠ 0 ∧ (n : 𝓞 L) = d * c := by
  obtain ⟨d, k, hk, h⟩ := Algebra.IsAlgebraic.exists_smul_eq_mul ℤ (1 : 𝓞 L) hc
  refine ⟨k.natAbs, if 0 ≤ k then d else -d, by simpa using hk, ?_⟩
  have h' : (k : 𝓞 L) = c * d := by simpa [zsmul_eq_mul] using h
  rcases le_total 0 k with h0 | h0
  · have : ((k.natAbs : ℤ)) = k := Int.natAbs_of_nonneg h0
    have e : ((k.natAbs : ℕ) : 𝓞 L) = (k : 𝓞 L) := by
      rw [← this]; simp
    by_cases h1 : 0 ≤ k
    · simp only [h1, if_true]; rw [e, h', mul_comm]
    · exact absurd h0 h1
  · have : ((k.natAbs : ℤ)) = -k := Int.ofNat_natAbs_of_nonpos h0
    have e : ((k.natAbs : ℕ) : 𝓞 L) = -(k : 𝓞 L) := by
      have := congrArg (fun q : ℤ => (q : 𝓞 L)) this
      simpa using this
    by_cases h1 : 0 ≤ k
    · have : k = 0 := le_antisymm h0 h1
      exact absurd this hk
    · simp only [h1, if_false]; rw [e, h']; ring

theorem clear_int [Module.Projective (𝓞 L) B] (j : B →ₗ[𝓞 L] T) (h : IsBaseChange L j) :
    Function.Injective j ∧ ∀ t : T, ∃ (n : ℕ) (x : B), n ≠ 0 ∧ j x = n • t := by
  haveI : IsLocalizedModule (nonZeroDivisors (𝓞 L)) j :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors (𝓞 L)) L j).2 h
  constructor
  · intro x y hxy
    obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_iff_exists (nonZeroDivisors (𝓞 L)) j).1 hxy
    have hc0 : (c : 𝓞 L) ≠ 0 := nonZeroDivisors.ne_zero c.2
    exact smul_right_injective B hc0 hc
  · intro t
    obtain ⟨⟨x, c⟩, hx⟩ := IsLocalizedModule.surj (nonZeroDivisors (𝓞 L)) j t
    obtain ⟨n, d, hn, hd⟩ := dvd_nat (c : 𝓞 L) (nonZeroDivisors.ne_zero c.2)
    refine ⟨n, d • x, hn, ?_⟩
    have : (n : 𝓞 L) • t = n • t := Nat.cast_smul_eq_nsmul _ _ _
    rw [← this, hd, map_smul, ← hx, mul_smul]
    rfl

theorem clear_span (j : B →ₗ[𝓞 L] T) {A : Type} (v : A → T) (S : Set B)
    (hS : ∀ l, ∃ (n : ℕ) (x : B), n ≠ 0 ∧ x ∈ S ∧ j x = n • v l) (w : T)
    (hw : w ∈ Submodule.span L (Set.range v)) :
    ∃ (d : 𝓞 L) (y : B), d ≠ 0 ∧ y ∈ Submodule.span (𝓞 L) S ∧ j y = d • w := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, rfl⟩ := hx
    obtain ⟨n, x, hn, hx, hj⟩ := hS l
    refine ⟨n, x, by exact_mod_cast hn, Submodule.subset_span hx, ?_⟩
    rw [hj]; exact (Nat.cast_smul_eq_nsmul _ _ _).symm
  | zero => exact ⟨1, 0, one_ne_zero, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d, a, hd, ha, hja⟩ := hx
    obtain ⟨d', a', hd', ha', hja'⟩ := hy
    refine ⟨d * d', d' • a + d • a', mul_ne_zero hd hd',
      add_mem (Submodule.smul_mem _ _ ha) (Submodule.smul_mem _ _ ha'), ?_⟩
    rw [map_add, map_smul, map_smul, hja, hja', smul_add, smul_smul, smul_smul, mul_comm d' d]
  | smul s x _ hx =>
    obtain ⟨d, a, hd, ha, hja⟩ := hx
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) s
    have hq0 : (q : 𝓞 L) ≠ 0 := nonZeroDivisors.ne_zero hq
    have hq1 : algebraMap (𝓞 L) L q ≠ 0 := by simpa using hq0
    refine ⟨q * d, p • a, mul_ne_zero hq0 hd, Submodule.smul_mem _ _ ha, ?_⟩
    rw [map_smul, hja, ← algebraMap_smul L p (d • x), ← algebraMap_smul L (q * d) _]
    rw [← algebraMap_smul L d x, smul_smul, smul_smul, map_mul]
    congr 1
    field_simp

end Clear

section Val

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {R : Type} [CommRing R] [IsLocalRing R] {z : Sp R ⟶ X}

theorem val_unique (hξ : IsCptGen ξ) {a : Ω} {r r' : R} (h : ValAt ξ z a r) (h' : ValAt ξ z a r') : r = r' := by
  obtain ⟨h1, s, hs, rfl⟩ := h
  obtain ⟨h2, s', hs', rfl⟩ := h'
  have : s = s' := hξ.inj ⟨centre z, h1⟩ (hs.trans hs'.symm)
  rw [this]

theorem val_mul {a a' : Ω} {r r' : R} (h : ValAt ξ z a r) (h' : ValAt ξ z a' r') :
    ValAt ξ z (a * a') (r * r') := by
  obtain ⟨h1, s, rfl, rfl⟩ := h
  obtain ⟨h2, s', rfl, rfl⟩ := h'
  exact ⟨h1, s * s', map_mul _ _ _, map_mul _ _ _⟩

theorem val_exists (h : genPt ξ ⤳ centre z) {a : Ω} (ha : a ∈ regAt ξ ⟨centre z, h⟩) : ∃ r, ValAt ξ z a r := by
  obtain ⟨s, rfl⟩ := ha
  exact ⟨_, h, s, rfl, rfl⟩

theorem val_zero (h : genPt ξ ⤳ centre z) : ValAt ξ z (0 : Ω) (0 : R) := ⟨h, 0, map_zero _, map_zero _⟩

theorem val_one (h : genPt ξ ⤳ centre z) : ValAt ξ z (1 : Ω) (1 : R) := ⟨h, 1, map_one _, map_one _⟩

theorem reg_of_val {a : Ω} {r : R} (h : ValAt ξ z a r) (h' : genPt ξ ⤳ centre z) :
    a ∈ regAt ξ ⟨centre z, h'⟩ := by
  obtain ⟨_, s, rfl, -⟩ := h
  exact ⟨s, rfl⟩

theorem inv_nat_reg {F : Type} [Field F] [CharZero F] {z : Sp F ⟶ X} (h : genPt ξ ⤳ centre z) {m : ℕ} (hm : 0 < m) :
    (m : Ω)⁻¹ ∈ regAt ξ ⟨centre z, h⟩ ∧ (m : Ω) ≠ 0 := by
  let f : X.presheaf.stalk (centre z) →+* F := (Scheme.stalkClosedPointTo z).hom
  haveI : IsLocalHom f := inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo z).hom)
  have hu : IsUnit (f (m : X.presheaf.stalk (centre z))) := by
    rw [map_natCast f m]
    exact (Nat.cast_ne_zero.2 hm.ne' : (m : F) ≠ 0).isUnit
  obtain ⟨u, hu⟩ := (isUnit_map_iff f _).1 hu
  have e : (m : Ω) * genMap ξ ⟨centre z, h⟩ ((u⁻¹ : (X.presheaf.stalk (centre z))ˣ) : X.presheaf.stalk (centre z)) = 1 := by
    rw [← map_natCast (genMap ξ ⟨centre z, h⟩) m, ← hu, ← map_mul]
    simp
  have h0 : (m : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one e
  refine ⟨⟨_, eq_inv_of_mul_eq_one_right e⟩, h0⟩

end Val

theorem exists_phi : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (V : Lat ξ Li) (r : ℕ) (b₀ : Fin r → Li)
    (m : ℕ) (i : Fin r) (a : K → ℤ) (e₀ : Ω),
    CharZero Ω → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → 0 < m →
    LinearIndependent Ω b₀ → Sandwich M V b₀ m → (V.gr b₀ i).IsDegOn Set.univ y a e₀ →
    ∀ (L : Type) [Field L] [NumberField L] (w : (Σ k, J k) → L) (z : Sp (𝓞 L) ⟶ X),
      CoordsAt ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) w → ∀ (B : HermitianBundle.{0} L) (MB : LieModel G z B.carrier)
      (F₀ F₁ : Submodule (𝓞 L) B.carrier), IsSubFibre M (flagStep Ω b₀ i) z MB F₀ →
      IsSubFibre M (flagStep Ω b₀ (i + 1)) z MB F₁ → ∀ c₀ : (k : K) → J k, (∀ k, w ⟨k, c₀ k⟩ ≠ 0) →
      ∃ φ : F₁ →ₗ[𝓞 L] L, (∀ x, φ x = 0 ↔ (x : B.carrier) ∈ F₀) ∧
        (∀ (x : F₁) (e : Li) (v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G) (t : Ω) (u : L),
          e ∈ flagStep Ω b₀ (i + 1) → M.ValAt _ e v → MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) (x : B.carrier) v →
          IsCls b₀ i e t → ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (t / gen y a e₀ c₀) u → φ x = u) := by
  intro X Ω _ ξ K _ J _ y G _ _ _ Li _ _ M V r b₀ m i a e₀ _hc hq hT hm hb₀ hS hD L _ _ w z hw B MB F₀ F₁ hF₀ hF₁ c₀ hc₀
  have hξ : IsCptGen ξ := hT.gen
  obtain ⟨zL, hzL⟩ : ∃ zL, zL = spMap (algebraMap (𝓞 L) L) ≫ z := ⟨_, rfl⟩
  rw [← hzL] at hw ⊢
  have hp : genPt ξ ⤳ centre zL := hq _
  have hIC : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c₀ ⟨centre zL, hp⟩ := by
    have hunit : ∀ k, IsUnit (w ⟨k, c₀ k⟩) := fun k => (hc₀ k).isUnit
    have hy : ∀ k, y ⟨k, c₀ k⟩ ≠ 0 := fun k => (hw.2 k (c₀ k) (hunit k)).1
    refine ⟨Finset.prod_ne_zero_iff.2 fun k _ => hy k, fun c' => ?_⟩
    show (∏ k, y ⟨k, c' k⟩) / (∏ k, y ⟨k, c₀ k⟩) ∈ regAt ξ _
    rw [← Finset.prod_div_distrib]
    refine prod_mem fun k _ => ?_
    obtain ⟨r', hr, -⟩ := (hw.2 k (c₀ k) (hunit k)).2 (c' k)
    exact reg_of_val hr hp
  obtain ⟨b, π, κ, hflag, -, hmb, hπ, hreg, hκ0, hκ, hκi, hcls⟩ :=
    GlobalTheory.T.exists_graded_sandwich_coordinates X Ω ξ K J y G Li M V r b₀ m i a e₀ hb₀ hS hD ⟨centre zL, hp⟩ c₀ hIC
  obtain ⟨hmi, hm0⟩ := inv_nat_reg (ξ := ξ) hp hm
  have hbl : ∀ l, b l ∈ M.lat ⟨centre zL, hp⟩ := fun l => by
    have h1 := (M.lat ⟨centre zL, hp⟩).smul_mem (⟨(m : Ω)⁻¹, hmi⟩ : regAt ξ ⟨centre zL, hp⟩) (hmb l)
    have h2 : (⟨(m : Ω)⁻¹, hmi⟩ : regAt ξ ⟨centre zL, hp⟩) • (m : Ω) • b l = b l := by
      show (m : Ω)⁻¹ • (m : Ω) • b l = b l
      rw [smul_smul, inv_mul_cancel₀ hm0, one_smul]
    rwa [h2] at h1
  have hπr : ∀ l, ∀ e ∈ M.lat ⟨centre zL, hp⟩, π l e ∈ regAt ξ ⟨centre zL, hp⟩ := fun l e he => by
    have h1 := mul_mem hmi (hreg l e he)
    rwa [← _root_.mul_assoc, inv_mul_cancel₀ hm0, _root_.one_mul] at h1
  obtain ⟨T, _, _, ⟨MT⟩⟩ := lieModel_exists X G L zL
  letI : Module (𝓞 L) T := Module.compHom T (algebraMap (𝓞 L) L)
  haveI : IsScalarTower (𝓞 L) L T := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  subst hzL
  obtain ⟨j₀, hj₀, -⟩ := GlobalTheory.T.lie_model_existsUnique_semilinear X G (𝓞 L) L (algebraMap (𝓞 L) L) z B.carrier T MB MT
  let j : B.carrier →ₗ[𝓞 L] T :=
    { toFun := j₀, map_add' := j₀.map_add, map_smul' := fun c x => j₀.map_smulₛₗ c x }
  have hjj : ∀ x, MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) x (MT.pt (j x)) := hj₀
  have hbc : IsBaseChange L j := GlobalTheory.T.lie_model_isBaseChange X G (𝓞 L) L z B.carrier T MB MT j hjj
  obtain ⟨hinj, hclr⟩ := clear_int j hbc
  obtain ⟨ev, hev, hevs, -⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring X G Ω ξ Li M L _ hp T MT hξ inferInstance
  obtain ⟨g, hg⟩ := GlobalTheory.T.lattice_regular_at_local_point X G Ω ξ Li M L _ hp T MT (π i) hξ (hπr i)
  obtain ⟨uκ, huκ⟩ := val_exists hp hκ
  obtain ⟨uκi, huκi⟩ := val_exists hp hκi
  have huκ0 : uκ ≠ 0 := by
    have h1 := val_mul huκ huκi
    rw [mul_inv_cancel₀ hκ0] at h1
    have h2 := val_unique hξ h1 (val_one hp)
    exact left_ne_zero_of_mul_eq_one h2
  have hdec : ∀ (n : ℕ) (e : Li) (he : e ∈ M.lat ⟨centre _, hp⟩), e ∈ flagStep Ω b n →
      ∃ ρ : Fin r → L, (∀ l, ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (π l e) (ρ l)) ∧ (∀ l : Fin r, n ≤ l → ρ l = 0) ∧
        ev ⟨e, he⟩ = ∑ l, ρ l • ev ⟨b l, hbl l⟩ := by
    intro n e he hn
    obtain ⟨h1, h2⟩ := flag_coord b π hπ n e hn
    choose ρ hρ using fun l => val_exists hp (hπr l e he)
    refine ⟨ρ, hρ, fun l hl => val_unique hξ (hρ l) (by rw [h2 l hl]; exact val_zero hp), ?_⟩
    have h3 : (⟨e, he⟩ : M.lat ⟨centre _, hp⟩) =
        ∑ l, (⟨π l e, hπr l e he⟩ : regAt ξ ⟨centre _, hp⟩) • (⟨b l, hbl l⟩ : M.lat ⟨centre _, hp⟩) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      exact h1
    rw [h3, map_sum]
    exact Finset.sum_congr rfl fun l _ => hevs _ _ _ (hρ l)
  have hval : ∀ (x : B.carrier) (e : Li) (v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G),
      M.ValAt _ e v → MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) x v →
      ∃ he : e ∈ M.lat ⟨centre _, hp⟩, ev ⟨e, he⟩ = j x := by
    intro x e v h1 h2
    have h3 : v = MT.pt (j x) := by
      apply Over.OverMorphism.ext
      have h4 := hjj x
      unfold LieModel.Lifts at h2 h4
      rw [Category.comp_id] at h2 h4
      exact h2.trans h4.symm
    subst h3
    exact (hev e (j x)).1 h1
  have hgv : ∀ (e : Li) (he : e ∈ M.lat ⟨centre _, hp⟩) (ρ : L),
      ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (π i e) ρ → g (ev ⟨e, he⟩) = ρ :=
    fun e he ρ h => hg e _ ρ ((hev e _).2 ⟨he, rfl⟩) h
  have hgs : ∀ (c : 𝓞 L) (x : B.carrier), g (j (c • x)) = algebraMap (𝓞 L) L c * g (j x) := by
    intro c x
    rw [map_smul, ← algebraMap_smul L c (j x), map_smul, smul_eq_mul]
  let φ : F₁ →ₗ[𝓞 L] L :=
    { toFun := fun x => uκ * g (j (x : B.carrier))
      map_add' := fun x x' => by simp [mul_add]
      map_smul' := fun c x => by
        simp only [Submodule.coe_smul, hgs, RingHom.id_apply, Algebra.smul_def]
        ring }
  have hφ : ∀ x : F₁, φ x = uκ * g (j (x : B.carrier)) := fun _ => rfl
  refine ⟨φ, fun x => ⟨fun h0 => ?_, fun hx => ?_⟩, ?_⟩
  · have hg0 : g (j (x : B.carrier)) = 0 := by
      rw [hφ] at h0
      exact (mul_eq_zero.1 h0).resolve_left huκ0
    obtain ⟨a₁, ha₁, hsp⟩ := (hF₁ x).1 x.2
    let W : Submodule L T := Submodule.span L
      (Set.range fun l : {l : Fin r // (l : ℕ) < i} => ev ⟨b l.1, hbl l.1⟩)
    have hWm : ∀ l : Fin r, (l : ℕ) < i → ev ⟨b l, hbl l⟩ ∈ W := fun l hl =>
      Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩
    have hW : ∀ t ∈ Submodule.span (𝓞 L) {x' | ∃ e ∈ flagStep Ω b₀ (i + 1),
        ∃ v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G,
        M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e v ∧ MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) x' v},
        j t - g (j t) • ev ⟨b i, hbl i⟩ ∈ W := by
      intro t ht
      induction ht using Submodule.span_induction with
      | mem t ht =>
        obtain ⟨e, he, v, h1, h2⟩ := ht
        obtain ⟨hl, hj⟩ := hval t e v h1 h2
        obtain ⟨ρ, hρ, hz, hs⟩ := hdec (i + 1) e hl (by rw [hflag]; exact he)
        rw [← hj, hgv e hl _ (hρ i), hs, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_sub_cancel_left]
        refine sum_mem fun l hl' => ?_
        have hne : l ≠ i := Finset.ne_of_mem_erase hl'
        rcases lt_or_ge (l : ℕ) i with h3 | h3
        · exact Submodule.smul_mem _ _ (hWm l h3)
        · have : (i : ℕ) + 1 ≤ l := by
            have : (l : ℕ) ≠ i := fun h => hne (Fin.ext h)
            omega
          rw [hz l this, zero_smul]
          exact zero_mem _
      | zero => simp
      | add t t' _ _ h1 h2 =>
        have := add_mem h1 h2
        convert this using 1
        simp only [map_add, add_smul]
        abel
      | smul c t _ h1 =>
        have := Submodule.smul_mem _ (algebraMap (𝓞 L) L c) h1
        convert this using 1
        rw [hgs, smul_sub, smul_smul, map_smul, algebraMap_smul]
    have h2 : j (a₁ • (x : B.carrier)) ∈ W := by
      have := hW _ hsp
      rwa [hgs, hg0, mul_zero, zero_smul, sub_zero] at this
    have hS₀ : ∀ l : {l : Fin r // (l : ℕ) < i}, ∃ (n : ℕ) (t : B.carrier), n ≠ 0 ∧
        t ∈ {x' | ∃ e ∈ flagStep Ω b₀ i, ∃ v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G,
          M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e v ∧ MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) x' v} ∧
        j t = n • ev ⟨b l.1, hbl l.1⟩ := by
      intro l
      obtain ⟨n, t, hn, ht⟩ := hclr (ev ⟨b l.1, hbl l.1⟩)
      have hnl : n • b l.1 ∈ M.lat ⟨centre _, hp⟩ := AddSubmonoid.nsmul_mem (M.lat ⟨centre _, hp⟩).toAddSubmonoid (hbl l.1) n
      refine ⟨n, t, hn, ⟨n • b l.1, ?_, MT.pt (j t), (hev _ _).2 ⟨hnl, ?_⟩, hjj t⟩, ht⟩
      · rw [← hflag]
        exact AddSubmonoid.nsmul_mem (flagStep Ω b i).toAddSubmonoid (Submodule.subset_span ⟨l.1, l.2, rfl⟩) n
      · rw [ht, ← map_nsmul]
        rfl
    obtain ⟨d, t, hd, ht, hjt⟩ := clear_span j _ _ hS₀ _ h2
    have h3 : t = d • a₁ • (x : B.carrier) := hinj (by rw [hjt]; exact (map_smul j d _).symm)
    exact (hF₀ x).2 ⟨d * a₁, mul_ne_zero hd ha₁, by rw [mul_smul, ← h3]; exact ht⟩
  · obtain ⟨a₁, ha₁, hsp⟩ := (hF₀ x).1 hx
    have hZ : ∀ t ∈ Submodule.span (𝓞 L) {x' | ∃ e ∈ flagStep Ω b₀ i,
        ∃ v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G,
        M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e v ∧ MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) x' v},
        g (j t) = 0 := by
      intro t ht
      induction ht using Submodule.span_induction with
      | mem t ht =>
        obtain ⟨e, he, v, h1, h2⟩ := ht
        obtain ⟨hl, hj⟩ := hval t e v h1 h2
        obtain ⟨ρ, hρ, hz, -⟩ := hdec i e hl (by rw [hflag]; exact he)
        rw [← hj, hgv e hl _ (hρ i), hz i le_rfl]
      | zero => simp
      | add t t' _ _ h1 h2 => simp [h1, h2]
      | smul c t _ h1 => rw [hgs, h1, mul_zero]
    have h1 := hZ _ hsp
    rw [hgs] at h1
    have h2 : algebraMap (𝓞 L) L a₁ ≠ 0 := by simpa using ha₁
    rw [hφ, (mul_eq_zero.1 h1).resolve_left h2, mul_zero]
  · intro x e v t u he h1 h2 hc hu
    obtain ⟨hl, hj⟩ := hval x e v h1 h2
    obtain ⟨ρ, hρ⟩ := val_exists hp (hπr i e hl)
    have h3 : g (j (x : B.carrier)) = ρ := by rw [← hj]; exact hgv e hl ρ hρ
    have h4 := val_mul hρ huκ
    rw [← hcls e t he hc] at h4
    rw [hφ, h3, val_unique hξ hu h4, mul_comm]

end GlobalTheory.CompanionTheory.Ar.RootHt.FinPhi
