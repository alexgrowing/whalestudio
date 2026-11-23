import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsForallAbvSubLt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProdUnifMulUnitIdl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleCharacterTrivialOnLocalUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
open Filter Topology

namespace GlobalTheory.FrobDense

variable {E : Type} [Field E] [NumberField E]

def abv (S : Finset (HeightOneSpectrum (𝓞 E))) : S ⊕ InfinitePlace E → AbsoluteValue E ℝ
  | Sum.inl v => GlobalTheory.LocalQuad.Approx.abv S (Sum.inl v)
  | Sum.inr w => w.1

theorem abv_isNontrivial (S : Finset (HeightOneSpectrum (𝓞 E))) (i : S ⊕ InfinitePlace E) :
    (abv S i).IsNontrivial := by
  rcases i with v | w
  · exact GlobalTheory.LocalQuad.Approx.abv_isNontrivial S (Sum.inl v)
  · exact InfinitePlace.isNontrivial _

theorem abv_not_isEquiv (S : Finset (HeightOneSpectrum (𝓞 E))) (v : S) (w : InfinitePlace E) :
    ¬ (abv S (Sum.inl v)).IsEquiv (abv S (Sum.inr w)) := by
  intro h
  have h1 : abv S (Sum.inl v) ((2 : ℕ) : E) ≤ 1 :=
    NumberField.HeightOneSpectrum.adicAbv_natCast_le_one E v.1 2
  rw [h.le_one_iff] at h1
  have h2 : abv S (Sum.inr w) ((2 : ℕ) : E) = 2 := by
    show w ((2 : ℕ) : E) = 2
    rw [← w.norm_embedding_eq, map_natCast]
    simp
  rw [h2] at h1
  norm_num at h1

theorem abv_pairwise (S : Finset (HeightOneSpectrum (𝓞 E))) :
    Pairwise fun i j ↦ ¬(abv S i).IsEquiv (abv S j) := by
  rintro (v | σ) (w | τ) hne h
  · exact GlobalTheory.LocalQuad.Approx.abv_pairwise S (i := Sum.inl v) (j := Sum.inl w)
      (fun e => hne (congrArg Sum.inl (Sum.inl_injective e))) h
  · exact abv_not_isEquiv S v τ h
  · exact abv_not_isEquiv S w σ h.symm
  · exact hne (congrArg Sum.inr (InfinitePlace.eq_iff_isEquiv.2 h))

abbrev Loc (S : Finset (HeightOneSpectrum (𝓞 E))) : Type :=
  ((w : InfinitePlace E) → w.Completion) × ((v : S) → v.1.adicCompletion E)

def proj (S : Finset (HeightOneSpectrum (𝓞 E))) : AdeleRing (𝓞 E) E →* Loc S where
  toFun a := (fun w => a.1 w, fun v => a.2 v.1)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem denseRange_inf (w : InfinitePlace E) : DenseRange (algebraMap E w.Completion) := by
  refine Dense.mono ?_ (InfinitePlace.Completion.denseRange_coe w)
  rintro _ ⟨a, rfl⟩
  exact ⟨WithAbs.equiv w.1 a, rfl⟩

theorem norm_inf (w : InfinitePlace E) (x : E) : ‖algebraMap E w.Completion x‖ = w x :=
  InfinitePlace.Completion.norm_coe w ((WithAbs.equiv w.1).symm x)

theorem denseRange_proj (S : Finset (HeightOneSpectrum (𝓞 E))) :
    DenseRange fun x : E => proj S (algebraMap E (AdeleRing (𝓞 E) E) x) := by
  refine Metric.denseRange_iff.2 fun y ε hε => ?_
  have hε2 : 0 < ε / 2 := half_pos hε
  choose a ha using fun v : S =>
    Metric.denseRange_iff.1 (HeightOneSpectrum.denseRange_algebraMap E v.1) (y.2 v) _ hε2
  choose b hb using fun w : InfinitePlace E =>
    Metric.denseRange_iff.1 (denseRange_inf w) (y.1 w) _ hε2
  obtain ⟨x, hx⟩ := GlobalTheory.LocalQuad.Approx.exists_forall_abv_sub_lt (abv_isNontrivial S) (abv_pairwise S)
    (Sum.elim a b) hε2
  refine ⟨x, ?_⟩
  rw [Prod.dist_eq, max_lt_iff, dist_pi_lt_iff hε, dist_pi_lt_iff hε]
  refine ⟨fun w => ?_, fun v => ?_⟩
  · have h1 : w (b w - x) < ε / 2 := hx (Sum.inr w)
    rw [← norm_inf, map_sub, ← dist_eq_norm] at h1
    have h2 := dist_triangle (y.1 w) (algebraMap E _ (b w)) (algebraMap E _ x)
    have h3 := hb w
    change dist (y.1 w) (algebraMap E _ x) < ε
    linarith
  · have h1 : GlobalTheory.LocalQuad.Approx.abv S (Sum.inl v) (a v - x) < ε / 2 := hx (Sum.inl v)
    rw [GlobalTheory.LocalQuad.Approx.abv_inl, map_sub, ← dist_eq_norm] at h1
    have h2 := dist_triangle (y.2 v) (algebraMap E _ (a v)) (algebraMap E _ x)
    have h3 := ha v
    change dist (y.2 v) (algebraMap E _ x) < ε
    linarith

theorem denseRange_units (S : Finset (HeightOneSpectrum (𝓞 E))) :
    DenseRange fun k : Eˣ => Units.map (proj S) (diagUnits E k) := by
  have hg : IsOpenEmbedding (Units.val : (Loc S)ˣ → Loc S) := Units.isOpenEmbedding_val
  rw [DenseRange, dense_iff_inter_open]
  rintro U hU ⟨u, hu⟩
  obtain ⟨k, v, hv, hk⟩ := (denseRange_proj S).exists_mem_open (hg.isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [map_zero] at hk
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    exact left_ne_zero_of_mul_eq_one (congrArg (fun y : Loc S => y.1 w) v.mul_inv)
      (congrArg (fun y : Loc S => y.1 w) hk)
  exact ⟨v, hv, Units.mk0 k hk0, Units.ext hk.symm⟩

def incl (S : Finset (HeightOneSpectrum (𝓞 E))) : Loc S →* AdeleRing (𝓞 E) E :=
  MonoidHom.prodMap (MonoidHom.id (InfiniteAdeleRing E))
    (∏ v : S, (Neutral.B1.finiteSingle E v.1).comp (Pi.evalMonoidHom (fun v : S => v.1.adicCompletion E) v))

theorem incl_snd (S : Finset (HeightOneSpectrum (𝓞 E))) (y : Loc S) :
    (incl S y).2 = ∏ v : S, Neutral.B1.finiteSingle E v.1 (y.2 v) :=
  MonoidHom.finsetProd_apply _ _ _

theorem continuous_incl (S : Finset (HeightOneSpectrum (𝓞 E))) : Continuous (incl S) := by
  refine Continuous.prodMk continuous_fst (?_ : Continuous fun y => (incl S y).2)
  simp only [incl_snd]
  exact continuous_finsetProd _ fun v _ =>
    (GlobalTheory.Mem.UnrAe.continuous_finSingle v.1).comp ((continuous_apply v).comp continuous_snd)

theorem incl_apply (S : Finset (HeightOneSpectrum (𝓞 E))) (y : Loc S) (v : S) : (incl S y).2 v.1 = y.2 v := by
  classical
  let e : FiniteAdeleRing (𝓞 E) E →* v.1.adicCompletion E :=
    (GlobalTheory.Mem.LocTriv.ev v.1).comp (MonoidHom.inr (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))
  show e (incl S y).2 = _
  rw [incl_snd, map_prod, Finset.prod_eq_single_of_mem v (Finset.mem_univ v)]
  · exact Function.update_self v.1 (y.2 v) (fun w : HeightOneSpectrum (𝓞 E) => (1 : w.adicCompletion E))
  · intro w _ hw
    exact Function.update_of_ne (fun h => hw (Subtype.ext h.symm)) (y.2 w)
      (fun w : HeightOneSpectrum (𝓞 E) => (1 : w.adicCompletion E))

theorem proj_incl (S : Finset (HeightOneSpectrum (𝓞 E))) (y : Loc S) : proj S (incl S y) = y :=
  Prod.ext rfl (funext fun v => incl_apply S y v)

variable {B : Type} [CommGroup B] [TopologicalSpace B] [T2Space B]

open GlobalTheory.Mem.LocTriv GlobalTheory.Mem.Chr GlobalTheory.Mem.Chr.IdlFact in

theorem eq_one_of_local (ψ : Ideles E →* B) (hψ : Continuous ψ) (a : Ideles E)
    (h1 : (a : AdeleRing (𝓞 E) E).1 = 1) (hl : ∀ v, ψ (localIdele E v (Units.map (ev v) a)) = 1) : ψ a = 1 := by
  have hp : ∀ (c : Ideles E) T, (∀ v, ψ (localIdele E v (Units.map (ev v) c)) = 1) → ψ (part c T) = 1 :=
    fun c T hc => by
      rw [part, map_prod]
      exact Finset.prod_eq_one fun v _ => hc v
  let T := (finite_valAt_ne_one a).toFinset
  let b := part a⁻¹ T * a
  have hb1 : ∀ v ∈ T, ev v (b : AdeleRing (𝓞 E) E) = 1 := fun v hv => by
    simp only [b]
    rw [Units.val_mul, map_mul, ev_part_mem _ hv, ← map_mul, Units.inv_mul, map_one]
  have hb2 : ∀ v ∉ T, ev v (b : AdeleRing (𝓞 E) E) = ev v (a : AdeleRing (𝓞 E) E) := fun v hv => by
    simp only [b]
    rw [Units.val_mul, map_mul, ev_part_not_mem _ hv, one_mul]
  have hbu : b ∈ unitIdl E := fun v => by
    show Valued.v (ev v (b : AdeleRing (𝓞 E) E)) = 1
    by_cases hv : v ∈ T
    · rw [hb1 v hv, map_one]
    · rw [hb2 v hv]
      have h : valAt v a = 1 := by simpa [T] using hv
      exact h
  have hbi : (b : AdeleRing (𝓞 E) E).1 = 1 := by
    show (part a⁻¹ T : AdeleRing (𝓞 E) E).1 * (a : AdeleRing (𝓞 E) E).1 = 1
    rw [part_fst, h1, one_mul]
  have hbl : ∀ v, ψ (localIdele E v (Units.map (ev v) b)) = 1 := fun v => by
    by_cases hv : v ∈ T
    · rw [show Units.map (ev v) b = 1 from Units.ext (hb1 v hv), map_one, map_one]
    · rw [show Units.map (ev v) b = Units.map (ev v) a from Units.ext (hb2 v hv), hl]
  have t := (hψ.tendsto b).comp (tendsto_part hbu fun w => congrFun hbi w)
  rw [show ψ ∘ part b = fun _ => 1 from funext fun S => hp b S hbl] at t
  have hb : ψ b = 1 := tendsto_nhds_unique t tendsto_const_nhds
  simp only [b] at hb
  rwa [← part_inv, map_mul, map_inv, hp a T hl, inv_one, one_mul] at hb

open GlobalTheory.Mem.LocTriv in

theorem eq_one_of_away (ψ : Ideles E →* B) (hψ : Continuous ψ) (hd : ∀ k, ψ (diagUnits E k) = 1)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (hS : ∀ v ∉ S, ∀ x, ψ (localIdele E v x) = 1) : ψ = 1 := by
  have h0 : ∀ a : Ideles E, Units.map (proj S) a = 1 → ψ a = 1 := fun a ha => by
    have e : proj S (a : AdeleRing (𝓞 E) E) = 1 := congrArg Units.val ha
    refine eq_one_of_local ψ hψ a (congrArg Prod.fst e) fun v => ?_
    by_cases hv : v ∈ S
    · rw [show Units.map (ev v) a = 1 from Units.ext (congrFun (congrArg Prod.snd e) ⟨v, hv⟩), map_one, map_one]
    · exact hS v hv _
  have h1 : ∀ a : Ideles E, ψ (Units.map (incl S) (Units.map (proj S) a)) = ψ a := fun a => by
    rw [← div_eq_one, ← map_div]
    refine h0 _ ?_
    rw [map_div, div_eq_one]
    exact Units.ext (proj_incl S _)
  have h2 : ∀ y, ψ (Units.map (incl S) y) = 1 := fun y =>
    (denseRange_units S).induction_on (p := fun y => ψ (Units.map (incl S) y) = 1) y
      (isClosed_eq (hψ.comp ((continuous_incl S).units_map _)) continuous_const) fun k => (h1 _).trans (hd k)
  ext a
  rw [← h1, h2, MonoidHom.one_apply]

omit [TopologicalSpace B] [T2Space B] in

theorem eq_one_of_unif {v : HeightOneSpectrum (𝓞 E)} (θ : (v.adicCompletion E)ˣ →* B)
    (h : ∀ x, IsUnifAt v x → θ x = 1) (x : (v.adicCompletion E)ˣ) : θ x = 1 := by
  obtain ⟨k, hk⟩ := exists_unif v
  generalize atFin v k = p at hk
  have hk' : Valued.v (p : v.adicCompletion E) = WithZero.exp (-1 : ℤ) := hk
  have hx : Valued.v (x : v.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).mpr x.ne_zero
  have hu : IsUnifAt v (x * p ^ (WithZero.log (Valued.v (x : v.adicCompletion E)) + 1)) := by
    show Valued.v _ = _
    rw [Units.val_mul, map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hk', ← WithZero.exp_zsmul]
    nth_rewrite 1 [← WithZero.exp_log hx]
    rw [← WithZero.exp_add]
    congr 1
    simp
  have := h _ hu
  rwa [map_mul, map_zpow, h p hk, one_zpow, mul_one] at this

theorem eq_one_of_frob : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (art : Ideles E →* Gab E Ω), IsGlobalArtin art → ∀ (B : Type) [CommGroup B] [TopologicalSpace B] [IsTopologicalGroup B] [T2Space B] (φ : G E Ω →* B), Continuous φ → ∀ S : Finset (HeightOneSpectrum (𝓞 E)), (∀ v, v ∉ S → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ : G E Ω, IsFrob (F := E) A (normV v) σ → φ σ = 1) → φ = 1 := by
  intro E Ω _ _ _ _ _ art ha B _ _ _ _ φ hφ S hS
  have h : (liftAb φ hφ).comp art = 1 := by
    refine eq_one_of_away _ ((continuous_liftAb φ hφ).comp ha.quot.continuous) (fun k => ?_) S fun v hv => ?_
    · have hk : diagUnits E k ∈ art.ker := by
        rw [ha.ker]
        exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
      rw [MonoidHom.comp_apply, MonoidHom.mem_ker.mp hk, map_one]
    · refine eq_one_of_unif (((liftAb φ hφ).comp art).comp (localIdele E v)) fun x hx => ?_
      obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
      obtain ⟨σ, hσ, e⟩ := (ha.frob v A hA _).mp ⟨x, hx, rfl⟩
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← e, liftAb_toAb, map_inv, hS v hv A hA σ hσ, inv_one]
  ext σ
  obtain ⟨x, hx⟩ := ha.quot.surjective (toAb E Ω σ)
  rw [← liftAb_toAb φ hφ, ← hx]
  exact DFunLike.congr_fun h x

end GlobalTheory.FrobDense
