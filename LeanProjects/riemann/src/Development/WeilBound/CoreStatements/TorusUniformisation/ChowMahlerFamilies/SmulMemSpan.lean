import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsLatticeFamily
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamilyModelBundlesStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeGoodBaseChangeStatement
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XChartNoethFrac
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XFamConstr
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ImageLatticeBaseChange
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.KernelLatticeBaseChange
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XSummandOfQuot
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XDotdualBc
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace PositivityTheory.Xgn.A_fam_good2

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
variable {V W : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup W] [Module Ω W]

theorem smul_mem_span (R : Subalgebra o Ω) (S : Set V) {a : Ω} (ha : a ∈ R) {e : V}
    (he : e ∈ spanOver R S) : a • e ∈ spanOver R S := by
  induction he using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, w, hw, rfl⟩ := hy
    rw [smul_smul]
    exact AddSubgroup.subset_closure ⟨_, mul_mem ha hb, w, hw, rfl⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add y w _ _ hy hw => rw [smul_add]; exact add_mem hy hw
  | neg y _ hy => rw [smul_neg]; exact neg_mem hy

theorem spanOver_eq (R : Subalgebra o Ω) (S : Set V) :
    spanOver R S = (Submodule.span R S).toAddSubgroup := by
  apply le_antisymm
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, e, he, rfl⟩
    exact (Submodule.span R S).smul_mem ⟨a, ha⟩ (Submodule.subset_span he)
  · intro v hv
    change v ∈ Submodule.span R S at hv
    induction hv using Submodule.span_induction with
    | mem y hy => exact AddSubgroup.subset_closure ⟨1, one_mem _, y, hy, (one_smul _ _).symm⟩
    | zero => exact zero_mem _
    | add y w _ _ hy hw => exact add_mem hy hw
    | smul a y _ hy => exact smul_mem_span R S a.2 hy

theorem map_spanOver (R : Subalgebra o Ω) (S : Set V) (f : V →ₗ[Ω] W) :
    (spanOver R S).map f.toAddMonoidHom = spanOver R (f '' S) := by
  rw [spanOver, spanOver, AddMonoidHom.map_closure]
  congr 1
  ext v
  constructor
  · rintro ⟨_, ⟨a, ha, e, he, rfl⟩, rfl⟩
    exact ⟨a, ha, _, ⟨e, he, rfl⟩, f.map_smul a e⟩
  · rintro ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩
    exact ⟨_, ⟨a, ha, e, he, rfl⟩, f.map_smul a e⟩

theorem bc_self {J : Type} (S : Set (J → Ω)) : bcMap Ω Ω J '' S = S := Set.image_id S

theorem bc_self_prod {J : Type} (S : Set (Ω × (J → Ω))) :
    Prod.map (algebraMap Ω Ω) (bcMap Ω Ω J) '' S = S := Set.image_id S

theorem gens (R : Subalgebra o Ω) (hR : IsNoetherianRing R) {N : ℕ} {L₀ : AddSubgroup V}
    (h₀ : LocFree R N L₀) (f : V →ₗ[Ω] W) (hf : Function.Surjective f) (L : AddSubgroup W)
    (hst : ∀ a ∈ R, ∀ v ∈ L, a • v ∈ L) (hle : ∀ v ∈ L, ∃ e ∈ L₀, f e = v) {b : Ω} (hb : b ≠ 0)
    (hge : ∀ e ∈ L₀, b • f e ∈ L) :
    ∃ S : Finset W, L = spanOver R (S : Set W) ∧ Submodule.span Ω (S : Set W) = ⊤ := by
  classical
  let L₀' : Submodule R V := { L₀ with smul_mem' := fun a e he => h₀.1 a a.2 e he }
  let L' : Submodule R W := { L with smul_mem' := fun a e he => hst a a.2 e he }
  obtain ⟨k, φ, v, hφ, hv⟩ := LocFreeProj.exists_dualBasis (L := L₀') (r := N) h₀
  have hfg : (Submodule.span R (Set.range fun i => f (v i))).FG :=
    Submodule.fg_span (Set.finite_range _)
  have hL : L' ≤ Submodule.span R (Set.range fun i => f (v i)) := by
    intro y hy
    obtain ⟨e, he, rfl⟩ := hle y hy
    rw [← hv e, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem _ (⟨φ i e, hφ i e he⟩ : R) (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨S, hS⟩ : L'.FG := hfg.of_le hL
  refine ⟨S, ?_, ?_⟩
  · rw [spanOver_eq, hS]
  · rw [eq_top_iff]
    intro y _
    obtain ⟨e, rfl⟩ := hf y
    rw [← hv e, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_smul]
    refine Submodule.smul_mem _ _ ?_
    have h1 : b • f (v i) ∈ L' := hge _ (v i).2
    rw [← hS] at h1
    have h2 := Submodule.smul_mem _ b⁻¹ (Submodule.span_le_restrictScalars R Ω _ h1 :
      b • f (v i) ∈ Submodule.span Ω (S : Set W))
    rwa [inv_smul_smul₀ hb] at h2

theorem annSub_min (n i : ℕ) : annSub Ω n (min i n) = annSub Ω n i := by
  unfold annSub
  congr 1
  ext j
  have := j.2
  simp only [Set.mem_setOf_eq]
  omega

theorem vanSub_min (F : Type) [Zero F] (n i : ℕ) : vanSub Ω F n (min i n) = vanSub Ω F n i := by
  unfold vanSub
  congr 1
  ext x
  refine forall_congr' fun j => ?_
  have := j.2
  have : min i n ≤ (j : ℕ) ↔ i ≤ (j : ℕ) := by omega
  rw [this]

theorem kk_min {F : Type} [Zero F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (τ : Sg)
    (i : ℕ) : D.kk τ (min i n) = D.kk τ i := by
  rw [LieLatticeData.kk, LieLatticeData.kk, vanSub_min]

theorem injective {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {x : (Σ k, ι k) → Ω} {d : ℕ}
    (h : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d) :
    Function.Injective (algebraMap O Ω) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have h1 : a ∈ (mcIdeal O x).comap (C : O →+* _) := by
    rw [Ideal.mem_comap, mcIdeal, RingHom.mem_ker]
    change GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcMap O x (algebraMap O _ a) = 0
    rw [AlgHom.commutes, MvPolynomial.algebraMap_apply, ha, map_zero]
  rw [h.2.2.1] at h1
  exact h1

theorem charData {O : Type} [CommRing O] [Algebra O Ω]
    (hinj : Function.Injective (algebraMap O Ω)) {F : Type} [Zero F] [One F] {Sg : Type} (p : ℕ)
    (hp : p.Prime) (w : O) (χ : Sg → F → O)
    (h : (p : O) ≠ 0 ∧ (∃ u : O, IsUnit u ∧ w ^ (p - 1) = u * (p : O)) ∧ ¬ IsUnit (p : O) ∧ (0 : F) ≠ 1 ∧
      ∀ τ, χ τ 0 = 0 ∧ χ τ 1 = 1) (R : Subalgebra O Ω) :
    CharData R p (algebraMap O Ω w) (fun τ a => algebraMap O Ω (χ τ a)) := by
  obtain ⟨h0, ⟨u, hu, hw⟩, -, h01, hχ⟩ := h
  obtain ⟨u, rfl⟩ := hu
  refine ⟨?_, R.algebraMap_mem _, ⟨algebraMap O Ω ((u⁻¹ : Oˣ) * w ^ (p - 2)), R.algebraMap_mem _, ?_⟩, h01,
    fun τ => ⟨?_, ?_, fun a => R.algebraMap_mem _⟩⟩
  · rw [← map_natCast (algebraMap O Ω)]
    exact (map_ne_zero_iff _ hinj).2 h0
  · have h2 : p - 1 = p - 2 + 1 := by have := hp.two_le; omega
    rw [← map_mul, mul_assoc, ← pow_succ, ← h2, hw, Units.inv_mul_cancel_left, map_natCast]
  · simp only [(hχ τ).1, map_zero]
  · simp only [(hχ τ).2, map_one]

section Point

variable {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ}
  (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (hR : IsNoetherianRing R) (p : ℕ) (w : Ω)
  (χ : Sg → F → Ω) (hχ : CharData R p w χ) (hB : D.Base R p w)

include hR hχ hB

theorem gens_dual (τ : Sg) (L : AddSubgroup (Fin (r τ) → Ω)) (hst : ∀ a ∈ R, ∀ v ∈ L, a • v ∈ L)
    (hle : ∀ m ∈ L, ∃ g, (g, m) ∈ D.Th τ) (hge : ∀ m, (0, m) ∈ D.Th τ → m ∈ L) :
    ∃ S : Finset (Fin (r τ) → Ω), L = spanOver R (S : Set (Fin (r τ) → Ω)) ∧ Submodule.span Ω (S : Set (Fin (r τ) → Ω)) = ⊤ :=
  gens R hR (PositivityTheory.Xgn.t_dotdual_bc R R (fun _ h => h) _ _ (hB.free τ).1).1 LinearMap.id
    Function.surjective_id L hst (fun m hm => ⟨m, ((hB.th τ).2.1 m).1 (hle m hm), rfl⟩) hχ.1
    fun e he => hge _ (((hB.th τ).2.2 _).2 ⟨e, he, rfl⟩)

theorem gens_kk (τ : Sg) (i : ℕ) (hst : ∀ a ∈ R, ∀ v ∈ D.kk τ i, a • v ∈ D.kk τ i) :
    ∃ S : Finset (Fin (r τ) → Ω), D.kk τ i = spanOver R (S : Set (Fin (r τ) → Ω)) ∧ Submodule.span Ω (S : Set (Fin (r τ) → Ω)) = ⊤ := by
  refine gens_dual D R hR p w χ hχ hB τ _ hst ?_ fun m hm => ⟨(0, m), ⟨hm, zero_mem _, trivial⟩, rfl⟩
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨v.1, hv.1⟩

theorem gens_step (τ : Sg) (i : Fin n)
    (hst : ∀ a ∈ R, ∀ v ∈ (D.stepGraph τ (χ τ) i).map (AddMonoidHom.snd _ _),
      a • v ∈ (D.stepGraph τ (χ τ) i).map (AddMonoidHom.snd _ _)) :
    ∃ S : Finset (Fin (r τ) → Ω), (D.stepGraph τ (χ τ) i).map (AddMonoidHom.snd _ _) =
      spanOver R (S : Set (Fin (r τ) → Ω)) ∧ Submodule.span Ω (S : Set (Fin (r τ) → Ω)) = ⊤ := by
  refine gens_dual D R hR p w χ hχ hB τ _ hst ?_ fun m hm => ⟨(0, m), ?_, rfl⟩
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨y, hy, z, hz, h⟩ := AddSubgroup.mem_sup.1 (AddSubgroup.mem_comap.1 hv)
    have h2 : y.2 + z.2 = v.2 := congrArg Prod.snd h
    have h3 : z.2 = 0 := hz.2
    rw [h3, add_zero] at h2
    refine ⟨y.1, ?_⟩
    change (y.1, v.2) ∈ _
    rw [← h2]
    exact hy
  · refine AddSubgroup.mem_comap.2 (AddSubgroup.mem_sup_left ?_)
    simpa using hm

theorem gens_im (τ : Sg) (hst : ∀ a ∈ R, ∀ v ∈ D.imH R p τ (χ τ), a • v ∈ D.imH R p τ (χ τ)) :
    ∃ S : Finset (Fin (s τ) → Ω), D.imH R p τ (χ τ) = spanOver R (S : Set (Fin (s τ) → Ω)) ∧
      Submodule.span Ω (S : Set (Fin (s τ) → Ω)) = ⊤ := by
  have hw : w ≠ 0 := by
    obtain ⟨hp, -, ⟨c, -, hc⟩, -⟩ := hχ
    rintro rfl
    exact hp (by simpa using hc)
  refine gens R hR (hB.free τ).2.2.2 (w⁻¹ • LinearMap.id) (fun v => ⟨w • v, inv_smul_smul₀ hw v⟩) _ hst
    ?_ hw fun e he => ?_
  · rintro _ ⟨v, hv, rfl⟩
    exact ⟨w • v.2, ((hB.del τ).2.1 _).1 ⟨v.1, hv.1⟩, inv_smul_smul₀ hw _⟩
  · exact ⟨(0, e), ⟨((hB.del τ).2.2.1 e).2 he, zero_mem _, trivial⟩, (smul_inv_smul₀ hw e).symm⟩

end Point

end PositivityTheory.Xgn.A_fam_good2

open PositivityTheory.Xgn.A_fam_good2 in
theorem PositivityTheory.Xgn.t_fam_good2 : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → fnField O x = ⊤ → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg x c ≠ 0 → ∀ τ, mulLat (algebraMap O Ω w) (stdLat (chartRing O (mseg x) c) _) ≤ (D c).af (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) → ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧ (∀ c, mseg (joinCoord x z) c ≠ 0 → (pullFamily O x z D c).Good₂ (chartRing O (mseg (joinCoord x z)) c) p (fun τ a => algebraMap O Ω (χ τ a))) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d hx hfn F _ _ _ n Sg _ r s p hp w χ φ D hD hG haf
  classical
  have hinj := injective hx
  obtain ⟨hno, -, hch⟩ := PositivityTheory.Xgn.t_chart_noeth_frac O Ω K ι x
  have hχ := charData hinj p hp w χ hD.char
  have hfam := (PositivityTheory.Xgn.t_fam_constr O Ω K ι x hinj p hp w χ φ D hD).2
  have hfr := fun c hc τ => ((GlobalTheory.T.lattice_good_base_change (D c) _ p _ _ (hχ _) (hD.base c hc) (hG c hc)).1 τ).1
  let I : Type := Sg ⊕ (Sg × Fin (n + 1)) ⊕ (Sg × Fin (n + 1)) ⊕ (Sg × Fin n) ⊕ Sg
  let M : I → ModuleCat.{0} Ω := fun j => match j with
    | .inl _ => ModuleCat.of Ω (Fin n → Ω)
    | .inr (.inl q) => ModuleCat.of Ω ((Fin n → Ω) ⧸ annSub Ω n q.2)
    | .inr (.inr (.inl q)) => ModuleCat.of Ω (Fin (r q.1) → Ω)
    | .inr (.inr (.inr (.inl q))) => ModuleCat.of Ω (Fin (r q.1) → Ω)
    | .inr (.inr (.inr (.inr τ))) => ModuleCat.of Ω (Fin (s τ) → Ω)
  let Γ : ∀ j, (∀ k, ι k) → AddSubgroup (M j) := fun j => match j with
    | .inl τ => fun c => (D c).af (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))
    | .inr (.inl q) => fun c => ((D c).af (chartRing O (mseg x) c) p
        (fun a => algebraMap O Ω (χ q.1 a))).map (annSub Ω n q.2).mkQ.toAddMonoidHom
    | .inr (.inr (.inl q)) => fun c => (D c).kk q.1 q.2
    | .inr (.inr (.inr (.inl q))) => fun c =>
        ((D c).stepGraph q.1 (fun a => algebraMap O Ω (χ q.1 a)) q.2).map (AddMonoidHom.snd _ _)
    | .inr (.inr (.inr (.inr τ))) => fun c =>
        (D c).imH (chartRing O (mseg x) c) p τ (fun a => algebraMap O Ω (χ τ a))
  obtain ⟨K', hK, hK', ι', hι', z, hz, hfree⟩ := GlobalTheory.T.lattice_family_model_bundles O Ω K ι x d hx hfn I
    (fun j => Module.finrank Ω (M j)) (fun j => M j) Γ (by
      rintro (τ | q | q | q | τ)
      · exact ⟨rfl, (hfam τ).1, fun c hc => gens _ (hno c) (hfr c hc τ) LinearMap.id Function.surjective_id
          _ (hfr c hc τ).1 (fun v hv => ⟨v, hv, rfl⟩) one_ne_zero fun e he => (one_smul Ω e).symm ▸ he⟩
      · have h := A_fam_constr.fam_map (hfam q.1).1 (annSub Ω n q.2).mkQ.toAddMonoidHom
          fun a v => (annSub Ω n q.2).mkQ.map_smul a v
        exact ⟨rfl, h, fun c hc => gens _ (hno c) (hfr c hc q.1) (annSub Ω n q.2).mkQ
          (Submodule.mkQ_surjective _) _ (h.1 c hc) (fun v hv => hv) one_ne_zero
          fun e he => ⟨e, he, (one_smul Ω _).symm⟩⟩
      · have h := (hfam q.1).2.2.1 q.2
        exact ⟨rfl, h, fun c hc => gens_kk (D c) _ (hno c) p _ _ (hχ _) (hD.base c hc) _ _ (h.1 c hc)⟩
      · have h := A_fam_constr.fam_map ((hfam q.1).2.1 q.2).2 (AddMonoidHom.snd _ _) fun a v => rfl
        exact ⟨rfl, h, fun c hc => gens_step (D c) _ (hno c) p _ _ (hχ _) (hD.base c hc) _ _ (h.1 c hc)⟩
      · have h := ((hfam τ).2.2.2.2 hG).2
        exact ⟨rfl, h, fun c hc => gens_im (D c) _ (hno c) p _ _ (hχ _) (hD.base c hc) _ (h.1 c hc)⟩)
  refine ⟨K', hK, hK', ι', hι', z, hz, fun c hc => ?_⟩
  obtain ⟨hc1, hle⟩ := (hch K' ι' z).2 c hc
  have hB := hD.base _ hc1
  have hG1 := hG _ hc1
  have e1 := fun τ => (((GlobalTheory.T.lattice_good_base_change _ _ p _ _ (hχ _) hB hG1).2 Ω _ hle).2 τ).1
  have e2 := PositivityTheory.Xgn.kernel_lattice_base_change _ _ p _ _ (hχ _) hB hG1 Ω _ hle
  have e3 := PositivityTheory.Xgn.image_lattice_base_change _ _ p _ _ (hχ _) hB hG1 (haf _ hc1) Ω _ hle
  simp only [bc_self, bc_self_prod, Algebra.algebraMap_self_apply] at e1 e2 e3
  unfold pullFamily
  refine ⟨fun τ i => ?_, fun τ i => ?_, fun τ i => ?_, fun τ => ?_⟩
  · rw [e1, ← annSub_min]
    refine (PositivityTheory.Xgn.summand_iff_locFree_quot _ _ _ (Module.finrank Ω ((Fin n → Ω) ⧸ annSub Ω n (min i n))) _
      (hfree (.inl τ) c hc)).1 ?_
    rw [map_spanOver]
    exact hfree (.inr (.inl (τ, ⟨min i n, by omega⟩))) c hc
  · have h := hfree (.inr (.inr (.inl (τ, ⟨min i n, by omega⟩)))) c hc
    change LocFree _ (Module.finrank Ω (Fin (r τ) → Ω)) _ at h
    rw [Module.finrank_fin_fun] at h
    rw [← kk_min, (e2 τ).1]
    exact h
  · rw [(e2 τ).2]
    have h := hfree (.inr (.inr (.inr (.inl (τ, i))))) c hc
    have e := map_spanOver (chartRing O (mseg (joinCoord x z)) c)
      ((D (restrictChart c)).stepGraph τ (fun a => algebraMap O Ω (χ τ a)) i : Set _)
      (LinearMap.snd Ω Ω (Fin (r τ) → Ω))
    change LocFree _ (Module.finrank Ω (Fin (r τ) → Ω)) _ at h
    rw [Module.finrank_fin_fun] at h
    exact e.symm ▸ h
  · have h := hfree (.inr (.inr (.inr (.inr τ)))) c hc
    change LocFree _ (Module.finrank Ω (Fin (s τ) → Ω)) _ at h
    rw [Module.finrank_fin_fun] at h
    rw [e3]
    exact h
