import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.KerGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.HomogSpan

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem coprod_rename_mem {O : Type} [CommRing O] {X : Type} [AddCommGroup X] {σ τ : Type} [Finite σ]
    (u : σ → τ) (wt : τ → X) (ws : σ → X) (h : ∀ s, wt (u s) = ws s) {j : X} {g : MvPowerSeries σ O}
    (hg : g ∈ wtPart O ws j) : rename u g ∈ wtPart O wt j := fun n hn => by
  rw [coeff_rename]
  refine Finset.sum_eq_zero fun d hd => hg d fun hj => hn ?_
  have hd' : Finsupp.mapDomain u d = n := by simpa using hd
  rw [← hd', ← hj, Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by rw [add_smul])]
  simp [h]

private theorem coprod_homog {O : Type} [CommRing O] {X : Type} [AddCommGroup X] {σ : Type} [Fintype σ]
    (wt : σ → X) {κ : Type} [Finite κ] (g : κ → MvPowerSeries σ O) (c : κ → X)
    (hg : ∀ i, g i ∈ wtPart O wt (c i)) : IsHomog O wt (Ideal.span (Set.range g)) := by
  have hp : ∀ i, g i ∈ (WPres.free O wt).part (c i) := fun i => ⟨g i, hg i, rfl⟩
  exact (homog_span O _ X (WPres.free O wt) κ (fun i => ⟨g i, (WPres.free O wt).part_le_A (hp i)⟩) c hp).1

private theorem coprod_ext {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] {R' : Type} [CommRing R'] [Algebra O R'] [IsCO O R'] {σ : Type} [Finite σ]
    (F G : MvPowerSeries σ O →ₐ[O] R') (hF : ∀ s, F (X s) ∈ maximalIdeal R') (h : ∀ s, G (X s) = F (X s)) :
    G = F :=
  (co_ev O O R' σ (Algebra.ofId O R') _ hF).unique ⟨fun x => G.commutes x, h⟩
    ⟨fun x => F.commutes x, fun _ => rfl⟩

theorem UpperTheory.V.Alg.coprod :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] (T : Type) [Fintype T] (B : T → Type) [∀ v, CommRing (B v)] [∀ v, Algebra O (B v)] [∀ v, IsCO O (B v)] (WB : ∀ v, WPres O X (B v)), (∀ v s, (WB v).z s ∈ maximalIdeal (B v)) →
      ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (i : ∀ v, B v →ₐ[O] R) (W : WPres O X R) (e : (Σ v, (WB v).σ) ≃ W.σ),
        (∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : ∀ v, B v →ₐ[O] R'), ∃! F : R →ₐ[O] R', ∀ v, F.comp (i v) = f v) ∧
        (∀ v s, W.wt (e ⟨v, s⟩) = (WB v).wt s ∧ W.z (e ⟨v, s⟩) = i v ((WB v).z s)) ∧ (∀ v j, ∀ x ∈ (WB v).part j, i v x ∈ W.part j) ∧
        RingHom.ker W.π = ⨆ v, (RingHom.ker (WB v).π).map (MvPowerSeries.rename fun s => e ⟨v, s⟩) := by
  intro O _ _ _ _ X _ T _ B _ _ _ WB hz
  classical
  let σ : Type := Σ v, (WB v).σ
  let wt : σ → X := fun p => (WB p.1).wt p.2
  let r : ∀ v, MvPowerSeries (WB v).σ O →ₐ[O] MvPowerSeries σ O :=
    fun v => rename fun s => (⟨v, s⟩ : σ)
  have hr : ∀ v j g, g ∈ wtPart O (WB v).wt j → r v g ∈ wtPart O wt j :=
    fun v j g hg => coprod_rename_mem _ wt _ (fun _ => rfl) hg
  have hrX : ∀ v s, r v (MvPowerSeries.X s) = MvPowerSeries.X ⟨v, s⟩ := fun v s => rename_X _ s
  let J : Ideal (MvPowerSeries σ O) := ⨆ v, (RingHom.ker (WB v).π).map (r v)
  have hJ : ∀ v g, (WB v).π g = 0 → r v g ∈ J := fun v g hg =>
    le_iSup (fun v => (RingHom.ker (WB v).π).map (r v)) v (Ideal.mem_map_of_mem _ hg)
  have hJm : J ≤ maximalIdeal _ := iSup_le fun v => Ideal.map_le_iff_le_comap.2 fun g hg hu => by
    have h1 : IsUnit g := by
      have h2 := isUnit_constantCoeff _ hu
      rw [isUnit_iff_constantCoeff]
      rwa [show constantCoeff (r v g) = constantCoeff g from constantCoeff_rename _ g] at h2
    have h3 := h1.map (WB v).π
    rw [show (WB v).π g = 0 from hg] at h3
    exact not_isUnit_zero h3
  have hJh : IsHomog O wt J := by
    choose n g c hg hs using fun v => ker_gen O X (WB v).σ (WB v).wt _ (WB v).homog
    have : J = Ideal.span (Set.range fun p : Σ v, Fin (n v) => r p.1 (g p.1 p.2)) := by
      rw [Set.range_sigma_eq_iUnion_range, Ideal.span_iUnion]
      refine iSup_congr fun v => ?_
      rw [hs v, Ideal.map_span, ← Set.range_comp]
      rfl
    rw [this]
    exact coprod_homog wt _ (fun p => c p.1 p.2) fun p => hr _ _ _ (hg p.1 p.2)
  haveI : IsCO O (MvPowerSeries σ O) := co_mvps O O σ
  haveI : Nontrivial (MvPowerSeries σ O ⧸ J) :=
    Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hJm)
  let π := Ideal.Quotient.mkₐ O J
  have hπ : Function.Surjective π := Ideal.Quotient.mkₐ_surjective O J
  have hk : RingHom.ker π = J := Ideal.Quotient.mkₐ_ker O J
  haveI hR : IsCO O (MvPowerSeries σ O ⧸ J) := co_quot O (MvPowerSeries σ O) _ π hπ
  let i : ∀ v, B v →ₐ[O] MvPowerSeries σ O ⧸ J := fun v =>
    (Ideal.Quotient.liftₐ (RingHom.ker (WB v).π) (π.comp (r v)) fun g hg =>
      Ideal.Quotient.eq_zero_iff_mem.2 (hJ v g hg)).comp
      (Ideal.quotientKerAlgEquivOfSurjective (WB v).surj).symm.toAlgHom
  have hi : ∀ v g, i v ((WB v).π g) = π (r v g) := fun v g => by
    have : (Ideal.quotientKerAlgEquivOfSurjective (WB v).surj).symm ((WB v).π g) = Ideal.Quotient.mk _ g := by
      rw [AlgEquiv.symm_apply_eq]; rfl
    simp only [i, AlgHom.comp_apply, AlgEquiv.coe_algHom]
    erw [this]
    rfl
  refine ⟨_, inferInstance, inferInstance, hR, i, ⟨σ, wt, π, hπ, by rw [hk]; exact hJh⟩, Equiv.refl _, ?_,
    fun v s => ⟨rfl, ?_⟩, ?_, hk⟩
  · intro R' _ _ _ f
    have ha : ∀ v s, f v ((WB v).z s) ∈ maximalIdeal R' := fun v s => by
      rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
      exact hz v s
    obtain ⟨F, ⟨-, hF⟩, -⟩ := co_ev O O R' σ (Algebra.ofId O R') (fun p => f p.1 ((WB p.1).z p.2))
      fun p => ha p.1 p.2
    have hFr : ∀ v, F.comp (r v) = (f v).comp (WB v).π := fun v =>
      coprod_ext _ _ (ha v) fun s => by rw [AlgHom.comp_apply, hrX, hF]; rfl
    have hFJ : ∀ g ∈ J, F g = 0 := by
      have : J ≤ RingHom.ker F := iSup_le fun v => Ideal.map_le_iff_le_comap.2 fun g hg => by
        show F.comp (r v) g = 0
        rw [hFr, AlgHom.comp_apply, show (WB v).π g = 0 from hg, map_zero]
      exact this
    refine ⟨Ideal.Quotient.liftₐ J F hFJ, fun v => ?_, fun G hG => ?_⟩
    · ext x
      obtain ⟨g, rfl⟩ := (WB v).surj x
      rw [AlgHom.comp_apply, hi]
      exact DFunLike.congr_fun (hFr v) g
    · have : G.comp π = F := coprod_ext _ _ (fun p => by rw [hF]; exact ha _ _) fun p => by
        rw [hF, ← hG, AlgHom.comp_apply, AlgHom.comp_apply, WPres.z, hi, hrX]
      ext x
      obtain ⟨g, rfl⟩ := hπ x
      exact DFunLike.congr_fun this g
  · show π _ = i v ((WB v).π _)
    rw [hi, hrX]
    rfl
  · rintro v j _ ⟨g, hg, rfl⟩
    exact ⟨r v g, hr v j g hg, (hi v g).symm⟩
