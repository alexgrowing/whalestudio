import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.MatchOne
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.MatchProd
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SplitLoc
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.PlaceUp

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Automorphic GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1
open scoped Classical

namespace UpperTheory.ConvolutionTheory.T

section Gen

variable {G : Type*} [Group G] [TopologicalSpace G]

private theorem ind_test [T2Space G] (U : Subgroup G) (hc : IsCompact (U : Set G)) (ho : IsOpen (U : Set G)) :
    IsLocallyConstant ((U : Set G).indicator (1 : G → ℂ)) ∧ HasCompactSupport ((U : Set G).indicator (1 : G → ℂ)) := by
  have hcl : IsClopen (U : Set G) := ⟨hc.isClosed, ho⟩
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_,
    HasCompactSupport.intro hc (fun x hx => Set.indicator_of_notMem hx _)⟩
  by_cases hx : x ∈ (U : Set G)
  · filter_upwards [ho.mem_nhds hx] with y hy
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
    rfl
  · filter_upwards [hcl.compl.isOpen.mem_nhds hx] with y hy
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

private theorem ind_left (U : Subgroup G) {u : G} (hu : u ∈ U) (g : G) :
    (U : Set G).indicator (1 : G → ℂ) (u * g) = (U : Set G).indicator (1 : G → ℂ) g := by
  by_cases h : g ∈ U
  · rw [Set.indicator_of_mem (show u * g ∈ (U : Set G) from U.mul_mem hu h),
      Set.indicator_of_mem (show g ∈ (U : Set G) from h)]
    rfl
  · have h' : u * g ∉ U := fun h' => h ((Subgroup.mul_mem_cancel_left U hu).1 h')
    rw [Set.indicator_of_notMem (show u * g ∉ (U : Set G) from h'),
      Set.indicator_of_notMem (show g ∉ (U : Set G) from h)]

private theorem exists_left_inv [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (φ : G → ℂ) (h1 : IsLocallyConstant φ) (h2 : HasCompactSupport φ) :
    ∃ B : OpenSubgroup G, ∀ b ∈ B, ∀ g, φ (b * g) = φ g := by
  have hK : IsCompact (tsupport φ) := h2
  have key : ∃ B : OpenSubgroup G, ∀ b ∈ B, ∀ y ∈ tsupport φ, φ (b * y) = φ y := by
    refine hK.induction_on (p := fun s => ∃ B : OpenSubgroup G, ∀ b ∈ B, ∀ y ∈ s, φ (b * y) = φ y)
      ⟨⊤, by simp⟩ ?_ ?_ ?_
    · rintro s t hst ⟨B, hB⟩
      exact ⟨B, fun b hb y hy => hB b hb y (hst hy)⟩
    · rintro s t ⟨B, hB⟩ ⟨C, hC⟩
      refine ⟨B ⊓ C, fun b hb y hy => ?_⟩
      have hb' := OpenSubgroup.mem_inf.1 hb
      rcases hy with hy | hy
      · exact hB b hb'.1 y hy
      · exact hC b hb'.2 y hy
    · intro x _
      have hW : IsOpen {z : G | φ (z * x) = φ x} :=
        (h1.isOpen_fiber (φ x)).preimage (continuous_mul_right x)
      have h1W : {z : G | φ (z * x) = φ x} ∈ nhds (1 : G) := hW.mem_nhds (by simp)
      obtain ⟨B, -, hB⟩ := exists_openSubgroup_isCompact_subset h1W
      refine ⟨{y | y * x⁻¹ ∈ B}, mem_nhdsWithin_of_mem_nhds ?_, B, ?_⟩
      · exact (B.isOpen.preimage (continuous_mul_right x⁻¹)).mem_nhds (by simp [one_mem])
      · intro b hb y hy
        have hy' : y * x⁻¹ ∈ B := hy
        have e1 : φ (b * (y * x⁻¹) * x) = φ x := hB (mul_mem hb hy')
        have e2 : φ ((y * x⁻¹) * x) = φ x := hB hy'
        simp only [mul_assoc, inv_mul_cancel, mul_one] at e1 e2
        rw [e1, e2]
  obtain ⟨B, hB⟩ := key
  refine ⟨B, fun b hb g => ?_⟩
  by_cases hg : g ∈ tsupport φ
  · exact hB b hb g hg
  · by_cases hbg : b * g ∈ tsupport φ
    · have := hB b⁻¹ (inv_mem hb) (b * g) hbg
      rw [inv_mul_cancel_left] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hg, image_eq_zero_of_notMem_tsupport hbg]

end Gen

section Semi

variable {ι : Type*} [Fintype ι] {R : ι → Type*} [∀ i, CommRing (R i)] [∀ i, TopologicalSpace (R i)]
  [∀ i, IsTopologicalRing (R i)] {n : ℕ}

private theorem ent (T : Type*) [CommRing T] [TopologicalSpace T] (a b : Fin n) :
    Continuous fun u : GL (Fin n) T => (u : Matrix (Fin n) (Fin n) T) a b :=
  (continuous_id.matrix_elem a b).comp Units.continuous_val

private theorem entInv (T : Type*) [CommRing T] [TopologicalSpace T] (a b : Fin n) :
    Continuous fun u : GL (Fin n) T => ((u⁻¹ : GL (Fin n) T) : Matrix (Fin n) (Fin n) T) a b :=
  (continuous_id.matrix_elem a b).comp Units.continuous_coe_inv

private def piGL : GL (Fin n) (∀ i, R i) ≃ₜ (∀ i, GL (Fin n) (R i)) where
  toFun g i := mapGL n (Pi.evalRingHom R i) g
  invFun x :=
    { val := Matrix.of fun a b i => ((x i : GL (Fin n) (R i)) : Matrix (Fin n) (Fin n) (R i)) a b
      inv := Matrix.of fun a b i => (((x i)⁻¹ : GL (Fin n) (R i)) : Matrix (Fin n) (Fin n) (R i)) a b
      val_inv := by
        ext a b i
        have h1 := congrFun (congrFun (Units.mul_inv (x i)) a) b
        simp only [Matrix.mul_apply] at h1
        simp only [Matrix.mul_apply, Finset.sum_apply, Matrix.of_apply, Pi.mul_apply]
        rw [h1]
        by_cases h : a = b <;> simp [h, Matrix.one_apply]
      inv_val := by
        ext a b i
        have h1 := congrFun (congrFun (Units.inv_mul (x i)) a) b
        simp only [Matrix.mul_apply] at h1
        simp only [Matrix.mul_apply, Finset.sum_apply, Matrix.of_apply, Pi.mul_apply]
        rw [h1]
        by_cases h : a = b <;> simp [h, Matrix.one_apply] }
  left_inv g := by
    ext a b i
    rfl
  right_inv x := by
    funext i
    ext a b
    rfl
  continuous_toFun := by
    refine continuous_pi fun i => ?_
    refine Units.continuous_iff.2 ⟨continuous_matrix fun a b => ?_, continuous_matrix fun a b => ?_⟩
    · exact (continuous_apply i).comp (ent (∀ i, R i) a b)
    · exact (continuous_apply i).comp (entInv (∀ i, R i) a b)
  continuous_invFun := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · refine continuous_matrix fun a b => continuous_pi fun i => ?_
      exact (ent (R i) a b).comp (continuous_apply i)
    · refine continuous_matrix fun a b => continuous_pi fun i => ?_
      exact (entInv (R i) a b).comp (continuous_apply i)

private theorem cont_ev (i : ι) : Continuous (mapGL n (Pi.evalRingHom R i)) :=
  (continuous_apply i).comp (piGL (R := R) (n := n)).continuous

private theorem compact_ev (C : ∀ i, Set (GL (Fin n) (R i))) (hC : ∀ i, IsCompact (C i)) :
    IsCompact {g : GL (Fin n) (∀ i, R i) | ∀ i, mapGL n (Pi.evalRingHom R i) g ∈ C i} := by
  have := (piGL (R := R) (n := n)).isCompact_preimage.2 (isCompact_univ_pi hC)
  convert this using 1
  ext g
  simp [piGL]

private theorem open_ev (C : ∀ i, Set (GL (Fin n) (R i))) (hC : ∀ i, IsOpen (C i)) :
    IsOpen {g : GL (Fin n) (∀ i, R i) | ∀ i, mapGL n (Pi.evalRingHom R i) g ∈ C i} := by
  have : {g : GL (Fin n) (∀ i, R i) | ∀ i, mapGL n (Pi.evalRingHom R i) g ∈ C i} =
      ⋂ i, mapGL n (Pi.evalRingHom R i) ⁻¹' C i := by
    ext g
    simp
  rw [this]
  exact isOpen_iInter_of_finite fun i => (hC i).preimage (cont_ev i)

private theorem compact_ev_one (i₀ : ι) (h : ∀ i, i = i₀) (K : Set (GL (Fin n) (R i₀))) (hK : IsCompact K) :
    IsCompact {g : GL (Fin n) (∀ i, R i) | mapGL n (Pi.evalRingHom R i₀) g ∈ K} := by
  have := compact_ev (n := n) (R := R) (Function.update (fun _ => Set.univ) i₀ K) (fun i => by
    obtain rfl := h i
    simpa using hK)
  convert this using 1
  ext g
  constructor
  · intro hg i
    obtain rfl := h i
    simpa using hg
  · intro hg
    simpa using hg i₀

end Semi

section Scale

variable {n : ℕ} {R S : Type*} [CommRing R] [CommRing S] [TopologicalSpace R]
  [MeasurableSpace (GL (Fin n) R)] [MeasurableSpace (GL (Fin n) S)]

private theorem orb_scale (μ : Measure (GL (Fin n) R)) (γ : GL (Fin n) R) (ν : Measure (Subgroup.centralizer {γ}))
    (a : ℂ) (f : GL (Fin n) R → ℂ) : orb μ γ ν (fun g => a * f g) = a * orb μ γ ν f := by
  unfold orb quotInt
  split_ifs with h
  · simp only [mul_assoc]
    rw [integral_const_mul]
  · simp

private theorem match_scale (ι : R →+* S) (s : S →+* S) (l : ℕ) (μS : Measure (GL (Fin n) S)) (μR : Measure (GL (Fin n) R))
    {a : ℂ} (ha : a ≠ 0) (φ : GL (Fin n) S → ℂ) (f : GL (Fin n) R → ℂ)
    (h : Match ι s l μS μR 1 φ (fun g => a * f g)) : Match ι s l μS μR a φ f := by
  intro γ hγ ν hν
  obtain ⟨h1, h2⟩ := h γ hγ ν hν
  refine ⟨fun δ hδ => ?_, fun hn => ?_⟩
  · rw [h1 δ hδ, orb_scale, one_mul]
  · have := h2 hn
    rw [orb_scale] at this
    exact (mul_eq_zero.1 this).resolve_left ha

end Scale

section Conv

variable {G : Type*} [Group G] [MeasurableSpace G]

private theorem cv_ind (μ : Measure G) (U : Subgroup G) (hU : MeasurableSet (U : Set G)) (c : ℂ) (x : G) :
    cv μ ((U : Set G).indicator (1 : G → ℂ)) (fun g => c * (U : Set G).indicator (1 : G → ℂ) g) x =
      ((μ.real (U : Set G) : ℂ) * c) * (U : Set G).indicator (1 : G → ℂ) x := by
  unfold cv
  by_cases hx : x ∈ U
  · have : (fun y => (U : Set G).indicator (1 : G → ℂ) y * (c * (U : Set G).indicator (1 : G → ℂ) (y⁻¹ * x))) =
        (U : Set G).indicator (fun _ => c) := by
      funext y
      by_cases hy : y ∈ U
      · have h' : y⁻¹ * x ∈ U := U.mul_mem (U.inv_mem hy) hx
        rw [Set.indicator_of_mem (show y ∈ (U : Set G) from hy), Set.indicator_of_mem (show y⁻¹ * x ∈ (U : Set G) from h'),
          Set.indicator_of_mem (show y ∈ (U : Set G) from hy)]
        simp
      · rw [Set.indicator_of_notMem (show y ∉ (U : Set G) from hy), Set.indicator_of_notMem (show y ∉ (U : Set G) from hy)]
        simp
    rw [this, integral_indicator_const _ hU, Set.indicator_of_mem (show x ∈ (U : Set G) from hx)]
    simp
  · have : (fun y => (U : Set G).indicator (1 : G → ℂ) y * (c * (U : Set G).indicator (1 : G → ℂ) (y⁻¹ * x))) = 0 := by
      funext y
      by_cases hy : y ∈ U
      · have h' : y⁻¹ * x ∉ U := fun h' => hx (by simpa using U.mul_mem hy h')
        rw [Set.indicator_of_notMem (show y⁻¹ * x ∉ (U : Set G) from h')]
        simp
      · rw [Set.indicator_of_notMem (show y ∉ (U : Set G) from hy)]
        simp
    rw [this, Set.indicator_of_notMem (show x ∉ (U : Set G) from hx)]
    simp

private theorem cvAll_ind (μ : Measure G) (U : Subgroup G) (hU : MeasurableSet (U : Set G)) (m : ℕ) :
    cvAll μ m (fun _ => (U : Set G).indicator (1 : G → ℂ)) =
      fun g => ((μ.real (U : Set G) : ℂ) ^ m) * (U : Set G).indicator (1 : G → ℂ) g := by
  induction m with
  | zero => funext g; simp [cvAll]
  | succ m ih =>
    funext g
    have : Fin.tail (fun _ : Fin (m + 1 + 1) => (U : Set G).indicator (1 : G → ℂ)) =
        fun _ : Fin (m + 1) => (U : Set G).indicator (1 : G → ℂ) := rfl
    simp only [cvAll, this, ih]
    rw [cv_ind μ U hU, pow_succ]
    ring

end Conv

private theorem ball_nhds {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (ρ : ValueGroupWithZero k) (h : 0 < ρ) : UpperTheory.ConvolutionTheory.Loc.ball n ρ ∈ nhds (1 : GL (Fin n) k) := by
  have : UpperTheory.ConvolutionTheory.Loc.ball n ρ =
      ⋂ i : Fin n, ⋂ j : Fin n, {g : GL (Fin n) k |
        valuation k ((g : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j) ≤ ρ} := by
    ext g
    simp [UpperTheory.ConvolutionTheory.Loc.ball]
  have ho : IsOpen (UpperTheory.ConvolutionTheory.Loc.ball (E := k) n ρ) := by
    rw [this]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact (GLnLocal.isOpen_valuation_le k h.ne').preimage ((GLnLocal.continuous_entry k n i j).sub continuous_const)
  exact ho.mem_nhds fun i j => by simp

private theorem small_level {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (U₀ : Subgroup (GL (Fin n) k)) (hU₀ : IsOpen (U₀ : Set (GL (Fin n) k))) {N : Set (GL (Fin n) k)}
    (hN : N ∈ nhds (1 : GL (Fin n) k)) :
    ∃ UF : Subgroup (GL (Fin n) k), IsCompact (UF : Set (GL (Fin n) k)) ∧ IsOpen (UF : Set (GL (Fin n) k)) ∧ UF ≤ U₀ ∧
      UF ≤ GLnLocal.integralGL k n ∧ (UF : Set (GL (Fin n) k)) ⊆ N := by
  obtain ⟨h1, h2, h3, h4⟩ := GLnLocal.isLocallyProfinite k n
  have hm : (U₀ : Set (GL (Fin n) k)) ∩ (GLnLocal.integralGL k n : Set (GL (Fin n) k)) ∩ N ∈ nhds (1 : GL (Fin n) k) :=
    Filter.inter_mem (Filter.inter_mem (hU₀.mem_nhds (one_mem U₀))
      ((GLnLocal.isOpen_integralGL k n).mem_nhds (one_mem _))) hN
  obtain ⟨K, hK, hs⟩ := exists_openSubgroup_isCompact_subset hm
  exact ⟨K.toSubgroup, hK, K.isOpen, fun x hx => (hs hx).1.1, fun x hx => (hs hx).1.2, fun x hx => (hs hx).2⟩

section Pack

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private def Pack (σ : E ≃ₐ[F] E) (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) (U₀ : Subgroup (GL (Fin n) (v.adicCompletion F)))
    (φ : GL (Fin n) (CompletionsOver E v) → ℂ) (f : GL (Fin n) (v.adicCompletion F) → ℂ) (c : ℂ)
    (UE : Subgroup (GL (Fin n) (CompletionsOver E v))) (UF : Subgroup (GL (Fin n) (v.adicCompletion F))) : Prop :=
  (IsLocallyConstant φ ∧ HasCompactSupport φ ∧ IsLocallyConstant f ∧ HasCompactSupport f) ∧
  (IsOpen (UE : Set (GL (Fin n) (CompletionsOver E v))) ∧ (UE : Set (GL (Fin n) (CompletionsOver E v))) ⊆ unitSet E n v ∧
    IsOpen (UF : Set (GL (Fin n) (v.adicCompletion F))) ∧ UF ≤ GLnLocal.integralGL (v.adicCompletion F) n) ∧
  ((∀ u ∈ UE, ∀ g, φ (u * g) = φ g) ∧ ∀ u ∈ UF, ∀ g, f (u * g) = f g) ∧
  GM.MatchAt σ v c φ f ∧ c ≠ 0 ∧ UF ≤ U₀ ∧ f = (UF : Set (GL (Fin n) (v.adicCompletion F))).indicator 1

private theorem matchAt_scale {σ : E ≃ₐ[F] E} {n : ℕ} {v : HeightOneSpectrum (𝓞 F)} {a : ℂ} (ha : a ≠ 0)
    {φ : GL (Fin n) (CompletionsOver E v) → ℂ} {f : GL (Fin n) (v.adicCompletion F) → ℂ}
    (h : GM.MatchAt σ v 1 φ (fun g => a * f g)) : GM.MatchAt σ v a φ f := by
  intro i1 i2 i3 i4 mE mF h1 h2 h3 h4
  exact match_scale _ _ _ _ _ ha _ _ (h mE mF h1 h2 h3 h4)

private theorem t2Space_generalLinearGroup_completionsOver (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) : T2Space (GL (Fin n) (CompletionsOver E v)) := by
  haveI : ∀ u : PlacesOver E v, T2Space (GL (Fin n) (u.1.adicCompletion E)) :=
    fun u => (GLnLocal.isLocallyProfinite (u.1.adicCompletion E) n).2.2.1
  exact (piGL (R := fun w : PlacesOver E v => w.1.adicCompletion E) (n := n)).isEmbedding.t2Space

private theorem pack_nonsplit [IsGalois F E] (σ : E ≃ₐ[F] E) (hσ : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) (n : ℕ)
    (v : HeightOneSpectrum (𝓞 F)) (w : PlacesOver E v) (hw : ∀ w' : PlacesOver E v, w' = w)
    (U₀ : Subgroup (GL (Fin n) (v.adicCompletion F))) (hU₀ : IsOpen (U₀ : Set (GL (Fin n) (v.adicCompletion F)))) :
    ∃ φ f c UE UF, Pack σ n v U₀ φ f c UE UF := by
  letI : MeasurableSpace (GL (Fin n) (CompletionsOver E v)) := borel _
  haveI : BorelSpace (GL (Fin n) (CompletionsOver E v)) := ⟨rfl⟩
  letI : MeasurableSpace (GL (Fin n) (v.adicCompletion F)) := borel _
  haveI : BorelSpace (GL (Fin n) (v.adicCompletion F)) := ⟨rfl⟩
  obtain ⟨mE, mF, hE, hF, -, -, hM⟩ := UpperTheory.ConvolutionTheory.T.matchOne F E σ n v
  obtain ⟨ρ, hρ, hup⟩ := UpperTheory.ConvolutionTheory.Loc.placeUp F E σ hσ v w hw n mE mF hE hF
  obtain ⟨UF, hc, ho, h0, hI, hb⟩ := small_level n U₀ hU₀ (ball_nhds n ρ hρ)
  obtain ⟨t1, t2⟩ := ind_test UF hc ho
  obtain ⟨φ₀, hφ₀, hm⟩ := hup _ ⟨t1, t2⟩ (fun x hx => hb (by by_contra hn; exact hx (Set.indicator_of_notMem hn _)))
  obtain ⟨l1, l2, l3, l4⟩ := GLnLocal.isLocallyProfinite (w.1.adicCompletion E) n
  obtain ⟨B, hB⟩ := exists_left_inv φ₀ hφ₀.1 hφ₀.2
  have hcont := cont_ev (n := n) (R := fun w : PlacesOver E v => w.1.adicCompletion E) w
  refine ⟨_, _, 1, (B.toSubgroup ⊓ GLnLocal.integralGL (w.1.adicCompletion E) n).comap (GM.cmp w), UF,
    ⟨⟨hφ₀.1.comp_continuous hcont, ?_, t1, t2⟩, ⟨?_, ?_, ho, hI⟩, ⟨?_, fun u hu g => ind_left UF hu g⟩,
      hM 1 _ _ hm, one_ne_zero, h0, rfl⟩⟩
  · haveI := t2Space_generalLinearGroup_completionsOver (E := E) n v
    have hK := compact_ev_one (n := n) (R := fun w : PlacesOver E v => w.1.adicCompletion E) w hw _ hφ₀.2
    exact HasCompactSupport.intro' hK hK.isClosed
      fun g hg => (show φ₀ _ = 0 from image_eq_zero_of_notMem_tsupport hg)
  · exact (B.isOpen.inter (GLnLocal.isOpen_integralGL _ n)).preimage hcont
  · intro g hg u
    obtain rfl := hw u
    exact hg.2
  · intro u hu g
    have := hB _ hu.1 (GM.cmp w g)
    simpa [GM.cmp] using this

private theorem pack_split [IsGalois F E] (σ : E ≃ₐ[F] E) (hσ : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) (m : ℕ)
    (hm : Module.finrank F E = m + 1) (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) (w₀ : PlacesOver E v) (hv : GM.Split E v)
    (U₀ : Subgroup (GL (Fin n) (v.adicCompletion F))) (hU₀ : IsOpen (U₀ : Set (GL (Fin n) (v.adicCompletion F)))) :
    ∃ φ f c UE UF, Pack σ n v U₀ φ f c UE UF := by
  letI : MeasurableSpace (GL (Fin n) (CompletionsOver E v)) := borel _
  haveI : BorelSpace (GL (Fin n) (CompletionsOver E v)) := ⟨rfl⟩
  letI iF : MeasurableSpace (GL (Fin n) (v.adicCompletion F)) := borel _
  haveI bF : BorelSpace (GL (Fin n) (v.adicCompletion F)) := ⟨rfl⟩
  obtain ⟨UF, hc, ho, h0, hI, -⟩ := small_level n U₀ hU₀ Filter.univ_mem
  obtain ⟨t1, t2⟩ := ind_test UF hc ho
  haveI := t2Space_generalLinearGroup_completionsOver (E := E) n v
  have hsl := fun u : PlacesOver E v => UpperTheory.ConvolutionTheory.L1.splitLoc F E v u (hv u) n
  have he₀ := fun u : PlacesOver E v => (hsl u).1
  choose e he using he₀
  let B : ∀ u : PlacesOver E v, Subgroup (GL (Fin n) (u.1.adicCompletion E)) := fun u =>
    UF.comap (e u).symm.toMulEquiv.toMonoidHom
  have hBm : ∀ (u : PlacesOver E v) x, x ∈ B u ↔ (e u).symm x ∈ UF := fun u x => Iff.rfl
  have hB : ∀ (u : PlacesOver E v) g, mapGL n (completionMap v u.1) g ∈ B u ↔ g ∈ UF := by
    intro u g
    rw [hBm, ← he u g]
    simp
  have hBc : ∀ u : PlacesOver E v, IsCompact (B u : Set (GL (Fin n) (u.1.adicCompletion E))) := fun u =>
    (e u).symm.toHomeomorph.isCompact_preimage.2 hc
  have hBo : ∀ u : PlacesOver E v, IsOpen (B u : Set (GL (Fin n) (u.1.adicCompletion E))) := fun u =>
    ho.preimage (e u).symm.continuous
  let h : ∀ u : PlacesOver E v, GL (Fin n) (u.1.adicCompletion E) → ℂ := fun u =>
    (B u : Set (GL (Fin n) (u.1.adicCompletion E))).indicator 1
  let UE : Subgroup (GL (Fin n) (CompletionsOver E v)) := ⨅ u, (B u).comap (GM.cmp u)
  have hUEm : ∀ g, g ∈ UE ↔ ∀ u, GM.cmp u g ∈ B u := by
    intro g
    simp [UE, Subgroup.mem_iInf]
  have hUEs : (UE : Set (GL (Fin n) (CompletionsOver E v))) =
      {g | ∀ u, mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) u) g ∈
        (B u : Set (GL (Fin n) (u.1.adicCompletion E)))} := by
    ext g
    exact hUEm g
  have hUEc : IsCompact (UE : Set (GL (Fin n) (CompletionsOver E v))) := by
    rw [hUEs]
    exact compact_ev _ hBc
  have hUEo : IsOpen (UE : Set (GL (Fin n) (CompletionsOver E v))) := by
    rw [hUEs]
    exact open_ev _ hBo
  have hφ : GM.prodFn h = (UE : Set (GL (Fin n) (CompletionsOver E v))).indicator 1 := by
    funext g
    unfold GM.prodFn
    rw [finprod_eq_prod_of_fintype]
    by_cases hg : g ∈ UE
    · rw [Set.indicator_of_mem (show g ∈ (UE : Set _) from hg)]
      refine Finset.prod_eq_one fun u _ => ?_
      show (B u : Set (GL (Fin n) (u.1.adicCompletion E))).indicator 1 (GM.cmp u g) = 1
      rw [Set.indicator_of_mem (show GM.cmp u g ∈ (B u : Set (GL (Fin n) (u.1.adicCompletion E))) from (hUEm g).1 hg u)]
      rfl
    · rw [Set.indicator_of_notMem (show g ∉ (UE : Set _) from hg)]
      obtain ⟨u, hu⟩ := not_forall.1 (fun hh => hg ((hUEm g).2 hh))
      exact Finset.prod_eq_zero (Finset.mem_univ u)
        (Set.indicator_of_notMem (show GM.cmp u g ∉ (B u : Set (GL (Fin n) (u.1.adicCompletion E))) from hu) _)
  obtain ⟨mE, mF, hE, hF, -, hF1, -⟩ := UpperTheory.ConvolutionTheory.T.matchOne F E σ n v
  obtain ⟨w, -, hM⟩ := UpperTheory.ConvolutionTheory.L1.matchProd F E σ hσ m hm n v w₀ hv
  have hht : ∀ u : PlacesOver E v, Continuous (h u) ∧ HasCompactSupport (h u) := fun u => by
    have := GLnLocal.isLocallyProfinite (u.1.adicCompletion E) n
    obtain ⟨-, -, l3, -⟩ := this
    obtain ⟨s1, s2⟩ := ind_test (B u) (hBc u) (hBo u)
    exact ⟨s1.continuous, s2⟩
  have hMA : GM.MatchAt σ v 1 (GM.prodFn h)
      (cvAll mF m fun i g => h (w i) (mapGL n (completionMap v (w i).1) g)) := by
    intro i1 i2 i3 i4 mE' mF' a1 a2 a3 a4
    exact @hM h hht iF bF mF hF hF1 i1 i2 i3 i4 mE' mF' a1 a2 a3 a4
  have hfun : (fun (i : Fin (m + 1)) g => h (w i) (mapGL n (completionMap v (w i).1) g)) =
      fun _ => (UF : Set (GL (Fin n) (v.adicCompletion F))).indicator (1 : GL (Fin n) (v.adicCompletion F) → ℂ) := by
    funext i g
    by_cases hg : g ∈ UF
    · rw [Set.indicator_of_mem (show g ∈ (UF : Set _) from hg)]
      exact Set.indicator_of_mem (show _ ∈ (B (w i) : Set (GL (Fin n) ((w i).1.adicCompletion E))) from (hB (w i) g).2 hg) _
    · rw [Set.indicator_of_notMem (show g ∉ (UF : Set _) from hg)]
      exact Set.indicator_of_notMem
        (show _ ∉ (B (w i) : Set (GL (Fin n) ((w i).1.adicCompletion E))) from fun hh => hg ((hB (w i) g).1 hh)) _
  rw [hfun, cvAll_ind mF UF ho.measurableSet m] at hMA
  obtain ⟨g1, g2, g3, g4⟩ := GLnLocal.isLocallyProfinite (v.adicCompletion F) n
  haveI := hF
  have hpos : mF.real (UF : Set (GL (Fin n) (v.adicCompletion F))) ≠ 0 := by
    have a1 : mF (UF : Set (GL (Fin n) (v.adicCompletion F))) ≠ 0 := ho.measure_ne_zero mF ⟨1, one_mem UF⟩
    have a2 : mF (UF : Set (GL (Fin n) (v.adicCompletion F))) ≠ ⊤ := hc.measure_lt_top.ne
    exact (ENNReal.toReal_pos a1 a2).ne'
  have ha : ((mF.real (UF : Set (GL (Fin n) (v.adicCompletion F))) : ℂ) ^ m) ≠ 0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.2 hpos)
  refine ⟨GM.prodFn h, _, _, UE, UF,
    ⟨?_, ⟨hUEo, ?_, ho, hI⟩, ⟨?_, fun u hu g => ind_left UF hu g⟩, matchAt_scale ha hMA, ha, h0, rfl⟩⟩
  · rw [hφ]
    obtain ⟨s1, s2⟩ := ind_test UE hUEc hUEo
    exact ⟨s1, s2, t1, t2⟩
  · intro g hg u
    have hu := (hUEm g).1 hg u
    have hx : (e u).symm (GM.cmp u g) ∈ UF := hu
    have := (((hsl u).2.1) ((e u).symm (GM.cmp u g))).2 (hI hx)
    rw [← he u] at this
    have h2 : GM.cmp u g ∈ GLnLocal.integralGL (u.1.adicCompletion E) n := by simpa using this
    exact h2
  · rw [hφ]
    exact fun u hu g => ind_left UE hu g

end Pack

theorem locUp : UpperTheory.ConvolutionTheory.T.LocUp := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn q w₀ S hq hS U₀ hU₀
  have hpl := UpperTheory.ConvolutionTheory.T.places F E hp
  obtain ⟨-, -, hne, huniq, -, -⟩ := hpl
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank F E = m + 1 := ⟨Module.finrank F E - 1, by have := hp.pos; omega⟩
  have hex : ∀ v : HeightOneSpectrum (𝓞 F), ∃ φ f c UE UF, Pack σ n v (U₀ v) φ f c UE UF := by
    intro v
    obtain ⟨w⟩ := hne v
    by_cases hv : GM.Split E v
    · exact pack_split σ hσ m hm n v w hv (U₀ v) (hU₀ v)
    · exact pack_nonsplit σ hσ n v w (huniq v hv w) (U₀ v) (hU₀ v)
  choose φ₁ f₁ c₁ UE₁ UF₁ hP using hex
  let unitG : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin n) (CompletionsOver E v)) := fun v =>
    ⨅ u : PlacesOver E v, (GLnLocal.integralGL (u.1.adicCompletion E) n).comap (GM.cmp u)
  have hunit : ∀ v, (unitG v : Set (GL (Fin n) (CompletionsOver E v))) = unitSet E n v := by
    intro v
    ext g
    simp [unitG, unitSet, Subgroup.mem_iInf, GM.cmp]
  let iwG : Subgroup (GL (Fin n) (CompletionsOver E q)) :=
    ⨅ u : PlacesOver E q, (GLnLocal.iwahori (u.1.adicCompletion E) n).comap (GM.cmp u)
  refine ⟨{
    S := S
    q_not := hq
    unr := hS
    φ := fun v => if v ∈ S then φ₁ v else if h : v = q then h ▸ GM.iwFn w₀ 0 else (unitSet E n v).indicator 1
    f := fun v => if v ∈ S then f₁ v else if h : v = q then h ▸ (GM.iwCoset q 0).indicator 1
      else (GLnLocal.integralGL (v.adicCompletion F) n : Set _).indicator 1
    c := fun v => if v ∈ S then c₁ v else 1
    UE := fun v => if v ∈ S then UE₁ v else if h : v = q then h ▸ iwG else unitG v
    UF := fun v => if v ∈ S then UF₁ v else if v = q then GLnLocal.iwahori (v.adicCompletion F) n
      else GLnLocal.integralGL (v.adicCompletion F) n
    test := fun v hv => by
      simp only [if_pos hv]
      exact (hP v).1
    lev := fun v hv => by
      simp only [if_pos hv]
      exact (hP v).2.1
    inv := fun v hv => by
      simp only [if_pos hv]
      exact (hP v).2.2.1
    mat := fun v hv => by
      simp only [if_pos hv]
      exact (hP v).2.2.2.1
    at_q := by
      simp only [if_neg hq, dif_pos, if_true]
      refine ⟨trivial, trivial, fun g => ?_, trivial⟩
      simp [iwG, Subgroup.mem_iInf]
    off := fun v hv hvq => by
      simp only [if_neg hv, dif_neg hvq, if_neg hvq]
      exact ⟨trivial, trivial, hunit v, trivial⟩ }, rfl, fun v hv => ?_⟩
  simp only [if_pos hv]
  exact ⟨(hP v).2.2.2.2.1, (hP v).2.2.2.2.2.1, (hP v).2.2.2.2.2.2⟩

end UpperTheory.ConvolutionTheory.T
