import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsAlgHomValuationSubring
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLieCoordinates
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsToJetEq

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SeriesValue

open ReciprocityTheory.ChartRestriction.G.Chart GlobalTheory.JetSer GlobalTheory.ChartBaseChange GlobalTheory.TorsionCharacter ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev addOf)

variable {V : Type} [CommRing V] {G : Over (Spec (CommRingCat.of V))} [GrpObj G] {d : ℕ}

theorem existsUnique_jet [IsLocalRing V] {x : Fam G (Fin d)} (hx : IsUnivChart G d x) {A B : Type} [CommRing A]
    [Algebra V A] [CommRing B] [Algebra V B] (q : A →ₐ[V] B) (hq : Function.Surjective q) {m : ℕ}
    (hJ : (RingHom.ker q) ^ (m + 1) = ⊥) (y : sp (R₀ := V) A ⟶ G) (hy : spMap q ≫ y = 1) :
    ∃! ψ : JetR V (Fin d) m →ₐ[V] A, (∀ j, q (ψ (zR m j)) = 0) ∧ y = spMap ψ ≫ x m := by
  obtain ⟨C⟩ := exists_chart G
  obtain ⟨h, hh, hqh⟩ := exists_pt_of_aug C q hq hJ y hy
  obtain ⟨k, hk, hqk⟩ := exists_pt_of_aug C (jetAug V (Fin d) m) (fun r => ⟨algebraMap _ _ r, AlgHom.commutes _ r⟩)
    (ker_jetAug_pow _ m) (x m) (chart_aug hx m)
  let h₀ := fibLift q (eps C) h hqh
  obtain ⟨ψ₀, ⟨ha, hψ₀⟩, hu⟩ := hx.2.2 (fib q) (fibFst q) m (fib_ker q hJ) (ReciprocityTheory.ChartRestriction.G.Chart.pt C h₀) (by
    rw [spMap_pt]
    exact pt_eps_self C)
  refine ⟨(fibSnd q).comp ψ₀, ⟨fun j => ?_, ?_⟩, ?_⟩
  · show q (fibSnd q (ψ₀ (zR m j))) = 0
    rw [fib_cond, show fibFst q (ψ₀ (zR m j)) = 0 from (AlgHom.congr_fun ha _).trans (jetAug_zR m j), map_zero]
  · rw [← spMap_comp, Category.assoc, ← hψ₀, spMap_pt, hh]
    rfl
  · rintro v ⟨hψa, hψ⟩
    have hv : q.comp v = (Algebra.ofId V B).comp (jetAug V (Fin d) m) := by
      refine jet_ext fun j => ?_
      show q (v (zR _ j)) = algebraMap V B (jetAug V _ m (zR m j))
      rw [hψa, jetAug_zR, map_zero]
    have hvk : h = v.comp k := by
      apply pt_injective C
      rw [← hh, hψ, hk, spMap_pt]
    have e := hu (fibLift q (jetAug V (Fin d) m) v hv) ⟨rfl, by
      rw [hk, spMap_pt]
      congr 1
      refine AlgHom.ext fun s => Subtype.ext (Prod.ext ?_ ?_)
      · exact (AlgHom.congr_fun hqk s).symm
      · exact AlgHom.congr_fun hvk s⟩
    rw [← e]
    rfl

variable {O : Type} [CommRing O] [Algebra V O]

variable (V O d) in

def jetIn (m : ℕ) : JetR V (Fin d) m →ₐ[V] JetR O (Fin 1 × Fin d) m :=
  jetLift V (RingHom.ker (jetAug O _ m)) (ker_jetAug_pow _ m) (fun j => zR m (0, j)) (fun _ => zR_mem_ker m _)

theorem jetIn_zR (m : ℕ) (j : Fin d) : jetIn V d O m (zR m j) = zR m (0, j) :=
  jetLift_zR _ _ _ _ j

def ValAt (x : Fam G (Fin d)) (u : PS O 1 d) {A : Type} [CommRing A] [Algebra O A] (m : ℕ)
    (g : Spec (CommRingCat.of A) ⟶ G.left) (z : Fin d → A) (k : A) : Prop :=
  ∃ ψ : JetR O (Fin 1 × Fin d) m →ₐ[O] A, (∀ q, ψ (zR m q) = z q.2) ∧
    g = Spec.map (CommRingCat.ofHom (ψ.toRingHom.comp (jetIn V d O m).toRingHom)) ≫ (x m).left ∧ k = ψ (toJet m u)

def HasVal (x : Fam G (Fin d)) (u : PS O 1 d) {A : Type} [CommRing A] [Algebra O A]
    (g : Spec (CommRingCat.of A) ⟶ G.left) (k : A) : Prop :=
  ∃ m z, ValAt x u m g z k

variable {x : Fam G (Fin d)} {u : PS O 1 d} {A : Type} [CommRing A] [Algebra O A]

omit [GrpObj G] in
theorem HasVal.map {g : Spec (CommRingCat.of A) ⟶ G.left} {k : A} (h : HasVal x u g k) {B : Type} [CommRing B]
    [Algebra O B] (θ : A →ₐ[O] B) : HasVal x u (Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ g) (θ k) := by
  obtain ⟨m, z, ψ, h1, h2, h3⟩ := h
  refine ⟨m, fun j => θ (z j), θ.comp ψ, fun q => congrArg θ (h1 q), ?_, congrArg θ h3⟩
  rw [h2, ← Category.assoc, ← Spec.map_comp]
  rfl

theorem ValAt.succ (hx : IsUnivChart G d x) {m : ℕ} {g : Spec (CommRingCat.of A) ⟶ G.left} {z : Fin d → A} {k : A}
    (h : ValAt x u m g z k) : ValAt x u (m + 1) g z k := by
  obtain ⟨ψ, h1, h2, h3⟩ := h
  refine ⟨ψ.comp (jetTruncR O _ m), fun q => h1 q, ?_, ?_⟩
  · have e : ((jetTruncR O (Fin 1 × Fin d) m).restrictScalars V).comp (jetIn V d O (m + 1)) =
        (jetIn V d O m).comp (jetTruncR V (Fin d) m) := jet_ext fun j => by
      show jetTruncR O _ m (jetIn V d O (m + 1) (zR _ j)) = jetIn V d O m (zR _ j)
      rw [jetIn_zR, jetIn_zR]
      rfl
    rw [h2, ← hx.1 m, Over.comp_left, ← Category.assoc, spMap_left, ← Spec.map_comp]
    refine congrArg (fun φ => Spec.map (CommRingCat.ofHom φ) ≫ (x (m + 1)).left) ?_
    exact RingHom.ext fun a => congrArg ψ (AlgHom.congr_fun e a).symm
  · rw [h3, AlgHom.comp_apply, ((jetAlg O _).2.1 m u).1]

theorem ValAt.mono (hx : IsUnivChart G d x) {m n : ℕ} (hmn : m ≤ n) {g : Spec (CommRingCat.of A) ⟶ G.left}
    {z : Fin d → A} {k : A} (h : ValAt x u m g z k) : ValAt x u n g z k := by
  induction n, hmn using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact ih.succ hx

omit [GrpObj G] in
theorem ValAt.nilpotent {m : ℕ} {g : Spec (CommRingCat.of A) ⟶ G.left}
    {z : Fin d → A} {k : A} (h : ValAt x u m g z k) : IsNilpotent (Ideal.span (Set.range z)) := by
  obtain ⟨ψ, h1, -, -⟩ := h
  refine ⟨m + 1, eq_bot_iff.2 ?_⟩
  have : Ideal.span (Set.range z) ≤ (RingHom.ker (jetAug O (Fin 1 × Fin d) m)).map ψ := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    rw [← h1 (0, j)]
    exact Ideal.mem_map_of_mem _ (zR_mem_ker m _)
  refine (Ideal.pow_right_mono this _).trans ?_
  rw [← Ideal.map_pow, ker_jetAug_pow, Ideal.map_bot]

theorem exists_common (hx : IsUnivChart G d x) {g g' : Spec (CommRingCat.of A) ⟶ G.left} {k k' : A}
    (h : HasVal x u g k) (h' : HasVal x u g' k') :
    ∃ (m : ℕ) (z z' : Fin d → A) (J : Ideal A), J ^ (m + 1) = ⊥ ∧ (∀ j, z j ∈ J) ∧ (∀ j, z' j ∈ J) ∧
      ValAt x u m g z k ∧ ValAt x u m g' z' k' := by
  obtain ⟨m, z, h⟩ := h
  obtain ⟨m', z', h'⟩ := h'
  obtain ⟨n, hn⟩ := (Commute.all _ _).isNilpotent_add h.nilpotent h'.nilpotent
  refine ⟨m + m' + n, z, z', Ideal.span (Set.range z) + Ideal.span (Set.range z'), ?_,
    fun j => Ideal.mem_sup_left (Ideal.subset_span ⟨j, rfl⟩), fun j => Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩),
    h.mono hx (by omega), h'.mono hx (by omega)⟩
  exact pow_eq_zero_of_le (by omega) hn

theorem HasVal.unique [IsLocalRing V] (hx : IsUnivChart G d x) {g : Spec (CommRingCat.of A) ⟶ G.left} {k k' : A}
    (h : HasVal x u g k) (h' : HasVal x u g k') : k = k' := by
  obtain ⟨m, z, z', J, hJ, hz, hz', ⟨ψ, h1, h2, h3⟩, ⟨ψ', h1', h2', h3'⟩⟩ := exists_common hx h h'
  let _ : Algebra V A := ((algebraMap O A).comp (algebraMap V O)).toAlgebra
  have : IsScalarTower V O A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let φ := (ψ.restrictScalars V).comp (jetIn V d O m)
  let φ' := (ψ'.restrictScalars V).comp (jetIn V d O m)
  let q := Ideal.Quotient.mkₐ V J
  have hφ : ∀ j, φ (zR m j) = z j := fun j => (congrArg ψ (jetIn_zR m j)).trans (h1 _)
  have hφ' : ∀ j, φ' (zR m j) = z' j := fun j => (congrArg ψ' (jetIn_zR m j)).trans (h1' _)
  have hq : ∀ j, q (φ (zR m j)) = 0 := fun j => by rw [hφ]; exact Ideal.Quotient.eq_zero_iff_mem.2 (hz j)
  have hq' : ∀ j, q (φ' (zR m j)) = 0 := fun j => by rw [hφ']; exact Ideal.Quotient.eq_zero_iff_mem.2 (hz' j)
  have e : φ = φ' := (existsUnique_jet hx q Ideal.Quotient.mk_surjective (m := m) ((congrArg (· ^ (m + 1)) (Ideal.mk_ker (I := J))).trans hJ)
    (spMap φ ≫ x m) (by
      have : q.comp φ = (Algebra.ofId V _).comp (jetAug V (Fin d) m) := jet_ext fun j => by
        rw [AlgHom.comp_apply, hq, AlgHom.comp_apply, jetAug_zR, map_zero]
      rw [← Category.assoc, spMap_comp, this, ← spMap_comp, Category.assoc, chart_aug hx, MonObj.comp_one])).unique
    ⟨hq, rfl⟩ ⟨hq', Over.OverMorphism.ext (h2.symm.trans h2')⟩
  have e' : ψ = ψ' := jet_ext fun r => by rw [h1, h1', ← hφ, ← hφ', e]
  rw [h3, h3', e']

theorem exists_hasVal [IsLocalRing V] (hx : IsUnivChart G d x) (u : PS O 1 d) (J : Ideal A) (hJ : IsNilpotent J)
    (g : specV (algebraMap V O) A ⟶ G)
    (hg : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ g.left =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ (1 : specV (algebraMap V O) A ⟶ G).left) :
    ∃ k, HasVal x u g.left k := by
  obtain ⟨m, hm⟩ := hJ
  have hJ : J ^ (m + 1) = ⊥ := pow_eq_zero_of_le (Nat.le_succ m) hm
  let _ : Algebra V A := ((algebraMap O A).comp (algebraMap V O)).toAlgebra
  have : IsScalarTower V O A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let q := Ideal.Quotient.mkₐ V J
  obtain ⟨φ, ⟨h1, h2⟩, -⟩ := existsUnique_jet hx q Ideal.Quotient.mk_surjective (m := m)
    ((congrArg (· ^ (m + 1)) (Ideal.mk_ker (I := J))).trans hJ) g (by
      rw [← MonObj.comp_one (spMap q)]
      exact Over.OverMorphism.ext hg)
  let ψ : JetR O (Fin 1 × Fin d) m →ₐ[O] A :=
    jetLift O J hJ (fun r => φ (zR m r.2)) (fun r => Ideal.Quotient.eq_zero_iff_mem.1 (h1 r.2))
  have e : φ = (ψ.restrictScalars V).comp (jetIn V d O m) := jet_ext fun j => by
    show _ = ψ (jetIn V d O m _)
    rw [jetIn_zR, jetLift_zR]
  refine ⟨_, m, fun j => φ (zR m j), ψ, fun r => jetLift_zR _ _ _ _ r, ?_, rfl⟩
  rw [h2, e]
  rfl

theorem hasVal_one (hx : IsUnivChart G d x) (hu : MvPowerSeries.constantCoeff u = 1) :
    HasVal x u (1 : specV (algebraMap V O) A ⟶ G).left (1 : A) := by
  let _ : Algebra V A := ((algebraMap O A).comp (algebraMap V O)).toAlgebra
  have : IsScalarTower V O A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ψ : JetR O (Fin 1 × Fin d) 0 →ₐ[O] A := (Algebra.ofId O A).comp (jetAug O _ 0)
  have hψ : ∀ r, ψ (zR 0 r) = 0 := fun r => by
    show algebraMap O A (jetAug O _ 0 _) = 0
    rw [jetAug_zR, map_zero]
  refine ⟨0, 0, ψ, hψ, ?_, ?_⟩
  · have e : (ψ.restrictScalars V).comp (jetIn V d O 0) = (Algebra.ofId V A).comp (jetAug V _ 0) := jet_ext fun j => by
      show ψ (jetIn V d O 0 _) = algebraMap V A (jetAug V _ 0 _)
      rw [jetIn_zR, hψ, jetAug_zR, map_zero]
    have : spMap ((ψ.restrictScalars V).comp (jetIn V d O 0)) ≫ x 0 = 1 := by
      rw [e, ← spMap_comp, Category.assoc, chart_aug hx, MonObj.comp_one]
    exact (congrArg (·.left) this).symm
  · show 1 = algebraMap O A (jetAug O _ 0 _)
    rw [((jetAlg O _).2.1 0 u).2, hu, map_one]

theorem HasVal.mul (hx : IsUnivChart G d x) {L : Fin d → PS V 2 d} (hL : IsLawOf x L)
    (hu : ev (n := 2) ![fun i => MvPowerSeries.map (algebraMap V O) (L i)] u =
      ev (n := 2) ![ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt O d 0] u * ev (n := 2) ![ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt O d 1] u)
    {g g' : specV (algebraMap V O) A ⟶ G} {k k' : A}
    (h : HasVal x u g.left k) (h' : HasVal x u g'.left k') : HasVal x u (g * g').left (k * k') := by
  obtain ⟨m, z, z', J, hJ, hz, hz', ⟨ψ, h1, h2, h3⟩, ⟨ψ', h1', h2', h3'⟩⟩ := exists_common hx h h'
  let _ : Algebra V A := ((algebraMap O A).comp (algebraMap V O)).toAlgebra
  have : IsScalarTower V O A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let Θ : JetR O (Fin 2 × Fin d) m →ₐ[O] A := jetLift O J hJ (fun r => ![z, z'] r.1 r.2) (by
    rintro ⟨i, j⟩
    fin_cases i
    exacts [hz j, hz' j])
  have hΘ : ∀ r, Θ (zR m r) = ![z, z'] r.1 r.2 := jetLift_zR _ _ _ _
  let Θv := (Θ.restrictScalars V).comp (jetCoeff V O (Fin 2 × Fin d) m)
  have sub : ∀ a : Pt O 2 d, (∀ j, MvPowerSeries.constantCoeff (a j) = 0) →
      ∃ ρ : JetR O (Fin 1 × Fin d) m →ₐ[O] JetR O (Fin 2 × Fin d) m, (∀ r, ρ (zR m r) = toJet m (a r.2)) ∧
        ρ (toJet m u) = toJet m (ev ![a] u) := fun a ha => by
    have H := (jetAlg O (Fin 2 × Fin d)).2.2.2.2 (Fin 1 × Fin d) (fun r => (![a] : Fin 1 → Pt O 2 d) r.1 r.2)
      (fun r => by rw [Subsingleton.elim r.1 0]; exact ha _) m
    obtain ⟨ρ, hρ⟩ := H.1
    exact ⟨ρ, fun r => (hρ r).trans (by rw [Subsingleton.elim r.1 0]; rfl), H.2 ρ hρ u⟩
  obtain ⟨ρ, hρ, hρu⟩ := sub (fun i => MvPowerSeries.map (algebraMap V O) (L i)) (fun i => const_map (hL.1 i))
  obtain ⟨ρ₀, hρ₀, hρ₀u⟩ := sub (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt O d 0) (gp_pt 0)
  obtain ⟨ρ₁, hρ₁, hρ₁u⟩ := sub (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt O d 1) (gp_pt 1)
  have e₀ : ψ = Θ.comp ρ₀ := jet_ext fun r => by
    rw [h1, AlgHom.comp_apply, hρ₀, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt, toJet_X, hΘ]; rfl
  have e₁ : ψ' = Θ.comp ρ₁ := jet_ext fun r => by
    rw [h1', AlgHom.comp_apply, hρ₁, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt, toJet_X, hΘ]; rfl
  obtain ⟨t, ht⟩ := exists_test jetAlg x 2
  obtain ⟨χ, hχ, hχ'⟩ := (hL.2 2 _ _ _ _ (ht 0) (ht 1)).2 m
  have key : ∀ (a : Pt V 2 d) (χ : JetR V (Fin d) m →ₐ[V] JetR V (Fin 2 × Fin d) m)
      (ρ : JetR O (Fin 1 × Fin d) m →ₐ[O] JetR O (Fin 2 × Fin d) m), (∀ j, χ (zR m j) = toJet m (a j)) →
      (∀ r, ρ (zR m r) = toJet m (MvPowerSeries.map (algebraMap V O) (a r.2))) →
      spMap (((Θ.comp ρ).restrictScalars V).comp (jetIn V d O m)) ≫ x m = spMap Θv ≫ spMap χ ≫ x m :=
    fun a χ ρ hχ hρ => by
      rw [← Category.assoc, spMap_comp]
      congr 2
      refine jet_ext fun j => ?_
      show Θ (ρ (jetIn V d O m _)) = Θ (jetCoeff V O _ m (χ _))
      rw [jetIn_zR, hρ, hχ, jetCoeff_toJet]
  have hg : ∀ (i : Fin 2) (ρ : JetR O (Fin 1 × Fin d) m →ₐ[O] JetR O (Fin 2 × Fin d) m),
      (∀ r, ρ (zR m r) = toJet m (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt O d i r.2)) →
      spMap (((Θ.comp ρ).restrictScalars V).comp (jetIn V d O m)) ≫ x m = spMap Θv ≫ t i m := fun i ρ hρ => by
    obtain ⟨χ, hχ, hχ'⟩ := (ht i).2 m
    rw [hχ']
    exact key _ χ ρ hχ fun r => (hρ r).trans (by
      unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt; rw [MvPowerSeries.map_X])
  have g0 : g = spMap Θv ≫ t 0 m := (Over.OverMorphism.ext (by rw [h2, e₀]; rfl)).trans (hg 0 ρ₀ hρ₀)
  have g1 : g' = spMap Θv ≫ t 1 m := (Over.OverMorphism.ext (by rw [h2', e₁]; rfl)).trans (hg 1 ρ₁ hρ₁)
  refine ⟨m, fun j => Θ (toJet m (MvPowerSeries.map (algebraMap V O) (L j))), Θ.comp ρ,
    fun r => congrArg Θ (hρ r), ?_, ?_⟩
  · have := key _ χ ρ hχ fun r => (hρ r).trans (by unfold addOf; rw [eval_standard_points_two])
    rw [← hχ', MonObj.comp_mul, ← g0, ← g1] at this
    exact (congrArg (·.left) this).symm
  · obtain ⟨τ, hτ, -⟩ := (jetAlg O (Fin 2 × Fin d)).1 m
    rw [h3, h3', e₀, e₁, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, hρu, hρ₀u, hρ₁u, hu, ← hτ (_ * _),
      map_mul, map_mul, hτ, hτ]

theorem exists_lim {R : Type} [CommRing R] (I : Ideal R) [IsPrecomplete I R] (x : ∀ e : ℕ, R ⧸ I ^ (e + 1))
    (hx : ∀ e, Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) (x (e + 1)) = x e) :
    ∃ y : R, ∀ e, Ideal.Quotient.mk (I ^ (e + 1)) y = x e := by
  choose a ha using fun e => Ideal.Quotient.mk_surjective (x e)
  have step : ∀ e, a e - a (e + 1) ∈ I ^ (e + 1) := fun e => by
    refine Ideal.Quotient.eq.1 ?_
    rw [ha, ← hx e, ← ha (e + 1), Ideal.Quotient.factor_mk]
  have cau : ∀ m n, m ≤ n → a m - a n ∈ I ^ (m + 1) := fun m n hmn => by
    induction n, hmn using Nat.le_induction with
    | base => rw [sub_self]; exact zero_mem _
    | succ n hmn ih =>
      have := add_mem ih (Ideal.pow_le_pow_right (Nat.succ_le_succ hmn) (step n))
      rwa [sub_add_sub_cancel] at this
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) a (fun {m n} hmn => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    exact Ideal.pow_le_pow_right (Nat.le_succ m) (cau m n hmn))
  refine ⟨L, fun e => ?_⟩
  have := hL (e + 1)
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
  have h₂ := add_mem (step e) this
  rw [sub_add_sub_cancel] at h₂
  rw [← ha e]
  exact (Ideal.Quotient.eq.2 h₂).symm

variable (V) in

def res {B : Type} [CommRing B] [Algebra O B] (θ : A →ₐ[O] B) :
    specV (algebraMap V O) B ⟶ specV (algebraMap V O) A :=
  Over.homMk (Spec.map (CommRingCat.ofHom θ.toRingHom)) (by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    exact congrArg (fun φ => Spec.map (CommRingCat.ofHom φ)) (RingHom.ext fun r => θ.commutes _))

def LimVal (x : Fam G (Fin d)) (u : PS O 1 d) (p : O) (g : Spec (CommRingCat.of A) ⟶ G.left) (k : A) : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra O R] (θ : A →ₐ[O] R), IsNilpotent (algebraMap O R p) →
    HasVal x u (Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ g) (θ k)

variable {p : O}

omit [GrpObj G] in
theorem LimVal.map {g : Spec (CommRingCat.of A) ⟶ G.left} {k : A} (h : LimVal x u p g k) {B : Type} [CommRing B]
    [Algebra O B] (θ : A →ₐ[O] B) : LimVal x u p (Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ g) (θ k) := by
  intro R _ _ θ' hp
  have := h R (θ'.comp θ) hp
  rw [← Category.assoc, ← Spec.map_comp]
  exact this

theorem limVal_one (hx : IsUnivChart G d x) (hu : MvPowerSeries.constantCoeff u = 1) :
    LimVal x u p (1 : specV (algebraMap V O) A ⟶ G).left (1 : A) := by
  intro R _ _ θ _
  have e : (res V θ ≫ (1 : specV (algebraMap V O) A ⟶ G)).left = (1 : specV (algebraMap V O) R ⟶ G).left := by
    rw [MonObj.comp_one]
  rw [map_one]
  have h := hasVal_one (A := R) hx hu
  rw [← e] at h
  exact h

theorem LimVal.mul (hx : IsUnivChart G d x) {L : Fin d → PS V 2 d} (hL : IsLawOf x L)
    (hu : ev (n := 2) ![fun i => MvPowerSeries.map (algebraMap V O) (L i)] u =
      ev (n := 2) ![ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt O d 0] u * ev (n := 2) ![ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt O d 1] u)
    {g g' : specV (algebraMap V O) A ⟶ G} {k k' : A}
    (h : LimVal x u p g.left k) (h' : LimVal x u p g'.left k') : LimVal x u p (g * g').left (k * k') := by
  intro R _ _ θ hp
  have := HasVal.mul hx hL hu (g := res V θ ≫ g) (g' := res V θ ≫ g') (h R θ hp) (h' R θ hp)
  rw [← MonObj.comp_mul, ← map_mul] at this
  exact this

theorem nilpotent_quot (p : O) (n : ℕ) :
    IsNilpotent (algebraMap O (A ⧸ Ideal.span {algebraMap O A p} ^ n) p) :=
  ⟨n, by
    rw [← Ideal.Quotient.mk_algebraMap, ← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n)⟩

theorem LimVal.unique [IsLocalRing V] (hx : IsUnivChart G d x) [IsHausdorff (Ideal.span {algebraMap O A p}) A]
    {g : Spec (CommRingCat.of A) ⟶ G.left} {k k' : A} (h : LimVal x u p g k) (h' : LimVal x u p g k') : k = k' := by
  refine sub_eq_zero.1 (IsHausdorff.haus' (I := Ideal.span {algebraMap O A p}) _ fun n => ?_)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact Ideal.Quotient.eq.1 ((h _ (Ideal.Quotient.mkₐ O _) (nilpotent_quot p n)).unique hx
    (h' _ (Ideal.Quotient.mkₐ O _) (nilpotent_quot p n)))

theorem exists_limVal [IsLocalRing V] (hx : IsUnivChart G d x) (u : PS O 1 d) (p : O)
    [IsPrecomplete (Ideal.span {algebraMap O A p}) A] (I : Ideal A) {m : ℕ}
    (hI : I ^ m ≤ Ideal.span {algebraMap O A p}) (g : specV (algebraMap V O) A ⟶ G)
    (hg : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ g.left =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ (1 : specV (algebraMap V O) A ⟶ G).left) :
    ∃ k, LimVal x u p g.left k := by
  let P : Ideal A := Ideal.span {algebraMap O A p}
  have ex : ∀ e : ℕ, ∃ k, HasVal x u (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mkₐ O (P ^ (e + 1))).toRingHom) ≫
      g.left) k := fun e => by
    let θ := Ideal.Quotient.mkₐ O (P ^ (e + 1))
    refine exists_hasVal hx u (I.map θ) ⟨m * (e + 1), eq_bot_iff.2 ?_⟩ (res V θ ≫ g) ?_
    · rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap, pow_mul]
      exact (Ideal.pow_right_mono hI _).trans fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
    · have e1 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map θ))) ≫ (res V θ).left =
          Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I.map θ) θ.toRingHom Ideal.le_comap_map)) ≫
            Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
        show Spec.map _ ≫ Spec.map _ = _
        rw [← Spec.map_comp, ← Spec.map_comp]
        rfl
      rw [← MonObj.comp_one (res V θ), Over.comp_left, Over.comp_left, ← Category.assoc, ← Category.assoc, e1,
        Category.assoc, Category.assoc, hg]
  choose k hk using ex
  obtain ⟨k₀, hk₀⟩ := exists_lim P k fun e => by
    have := (hk (e + 1)).map (Ideal.Quotient.factorₐ O (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))))
    rw [← Category.assoc, ← Spec.map_comp] at this
    exact this.unique hx (hk e)
  refine ⟨k₀, fun R _ _ θ ⟨n, hn⟩ => ?_⟩
  let θ' : (A ⧸ P ^ (n + 1)) →ₐ[O] R := Ideal.Quotient.liftₐ _ θ fun a ha => by
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, map_pow, θ.commutes, pow_succ, hn, zero_mul, mul_zero]
  have := (hk n).map θ'
  rw [← Category.assoc, ← Spec.map_comp, ← hk₀] at this
  exact this

end GlobalTheory.SeriesValue
