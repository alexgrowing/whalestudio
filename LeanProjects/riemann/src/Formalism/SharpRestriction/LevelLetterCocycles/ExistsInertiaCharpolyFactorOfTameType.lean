import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.PadicSubsetSums.StableGradedCounts.CardLtAddCardGtAddCardEq
import Formalism.PadicSubsetSums.StableGradedCounts.ContinuousCoeffCharpolyRev

noncomputable section

namespace Formalism.MainNotions.SumRepresentations

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal Topology

section BN

variable {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ}

theorem glRep_apply (ρ : Γ →* GL (Fin a) k) (g : Γ) :
    glRep ρ g = Matrix.toLin' ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) k) := rfl

theorem ss_of_isSSRep (ρ : Γ →* GL (Fin a) k) (h : IsSSRep ρ) :
    IsSemisimpleModule (MonoidAlgebra k Γ) (glRep ρ).asModule := by
  rw [← Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  refine ⟨fun W => ?_⟩
  obtain ⟨W', hW', hc⟩ := h W.toSubmodule (fun g v hv => W.apply_mem_toSubmodule g hv)
  refine ⟨⟨W', fun g v hv => hW' g v hv⟩, ?_, ?_⟩
  · rw [disjoint_iff]
    exact Subrepresentation.toSubmodule_injective hc.inf_eq_bot
  · rw [codisjoint_iff]
    exact Subrepresentation.toSubmodule_injective hc.sup_eq_top

theorem brauerNesbitt_matrix (ρ ρ' : Γ →* GL (Fin a) k) (h : IsSSRep ρ) (h' : IsSSRep ρ')
    (hc : ∀ g, ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) k).charpoly =
      ((ρ' g : GL _ _) : Matrix (Fin a) (Fin a) k).charpoly) :
    ∃ Pm : GL (Fin a) k, ∀ g, ρ' g = Pm⁻¹ * ρ g * Pm := by
  obtain ⟨e, he⟩ := Formalism.IrreducibleCountingLemmas.Z.brauer_nesbitt k Γ (Fin a → k) (Fin a → k) (glRep ρ) (glRep ρ')
    (ss_of_isSSRep ρ h) (ss_of_isSSRep ρ' h') (fun g => by
      rw [glRep_apply, glRep_apply, Matrix.charpoly_toLin', Matrix.charpoly_toLin']
      exact hc g)
  have h1 : LinearMap.toMatrix' (e.symm : (Fin a → k) →ₗ[k] (Fin a → k)) *
      LinearMap.toMatrix' (e : (Fin a → k) →ₗ[k] (Fin a → k)) = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    simp
  have h2 : LinearMap.toMatrix' (e : (Fin a → k) →ₗ[k] (Fin a → k)) *
      LinearMap.toMatrix' (e.symm : (Fin a → k) →ₗ[k] (Fin a → k)) = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    simp
  refine ⟨⟨_, _, h1, h2⟩, fun g => ?_⟩
  apply Units.ext
  show ((ρ' g : GL _ _) : Matrix (Fin a) (Fin a) k) =
    LinearMap.toMatrix' (e : (Fin a → k) →ₗ[k] (Fin a → k)) * ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) k) *
      LinearMap.toMatrix' (e.symm : (Fin a → k) →ₗ[k] (Fin a → k))
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
  have hg : (e : (Fin a → k) →ₗ[k] (Fin a → k)) ∘ₗ Matrix.toLin' ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) k) =
      Matrix.toLin' ((ρ' g : GL _ _) : Matrix (Fin a) (Fin a) k) ∘ₗ (e : (Fin a → k) →ₗ[k] (Fin a → k)) := he g
  rw [hg, LinearMap.comp_assoc]
  simp

end BN

section G1

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)

theorem placesOver_finite (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem closed_of_adic {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [TopologicalSpace O]
    [IsTopologicalRing O] (hO : IsAdic (IsLocalRing.maximalIdeal O)) {X : Type} [Fintype X]
    (T : Submodule O (X → O)) : IsClosed (T : Set (X → O)) := by
  classical
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro f hf
  have hf' : T.mkQ f ≠ 0 := by
    rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hf
  have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := (X → O) ⧸ T) (IsLocalRing.maximalIdeal O)
    (Ideal.IsPrime.ne_top inferInstance)
  have : ∃ n : ℕ, T.mkQ f ∉ (IsLocalRing.maximalIdeal O ^ n • ⊤ : Submodule O ((X → O) ⧸ T)) := by
    by_contra hcon
    push Not at hcon
    apply hf'
    have : T.mkQ f ∈ (⨅ n : ℕ, IsLocalRing.maximalIdeal O ^ n • ⊤ : Submodule O ((X → O) ⧸ T)) :=
      (Submodule.mem_iInf _).2 hcon
    rw [hK] at this
    exact (Submodule.mem_bot _).1 this
  obtain ⟨n, hn⟩ := this
  refine ⟨{g | ∀ x, g x - f x ∈ IsLocalRing.maximalIdeal O ^ n}, ?_, ?_, ?_⟩
  · intro g hg hgT
    apply hn
    have h1 : T.mkQ f = - T.mkQ (g - f) := by
      have h0 : T.mkQ g = 0 := (Submodule.Quotient.mk_eq_zero T).2 hgT
      rw [map_sub, h0]
      simp
    rw [h1]
    apply Submodule.neg_mem
    have h2 : g - f = ∑ x, (g x - f x) • (Pi.single x 1 : X → O) := by
      funext y
      simp [Finset.sum_apply, Pi.single_apply]
    rw [h2, map_sum]
    refine Submodule.sum_mem _ fun x _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem_smul (hg x) Submodule.mem_top
  · have : {g : X → O | ∀ x, g x - f x ∈ IsLocalRing.maximalIdeal O ^ n} =
        ⋂ x, (fun g : X → O => g x - f x) ⁻¹' ((IsLocalRing.maximalIdeal O ^ n : Ideal O) : Set O) := by
      ext g
      simp
    rw [this]
    refine isOpen_iInter_of_finite fun x => ?_
    exact ((isAdic_iff.1 hO).1 n).preimage ((continuous_apply x).sub continuous_const)
  · intro x
    simp

theorem T_closed (i : N.Loc) : IsClosed ((N.T i : Set (N.X i → N.O i))) :=
  closed_of_adic (N.O_adic i) (Subalgebra.toSubmodule (N.T i))

theorem heckePol_coeff_mem (i : N.Loc) (w : PlE H) (m : ℕ) :
    (fun x => (heckePol N i x w).coeff m) ∈ N.T i := by
  have : (fun x => (heckePol N i x w).coeff m) =
      (if m = R.nV then 1 else 0 : N.X i → N.O i) + ∑ k ∈ Finset.Icc 1 R.nV,
        ((-1 : N.O i) ^ k * ((normV w : ℕ) : N.O i) ^ (k * (k - 1) / 2) *
          (if m = R.nV - k then 1 else 0)) • (N.hT i w k : N.X i → N.O i) := by
    funext x
    simp only [heckePol, coeff_add, coeff_X_pow, finsetSum_coeff, coeff_C_mul, Pi.add_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    congr 1
    · split_ifs <;> rfl
    · refine Finset.sum_congr rfl fun k _ => ?_
      ring
  rw [this]
  refine Subalgebra.add_mem _ ?_ (Subalgebra.sum_mem _ fun k _ => Subalgebra.smul_mem _ (N.hT i w k).2 _)
  split_ifs
  · exact Subalgebra.one_mem _
  · exact Subalgebra.zero_mem _

def Cheb : Prop :=
  ∀ Sg : Set (PlE H), Sg.Finite →
    closure {σ : G H.E N.Om | ∃ w ∉ Sg, IsSplitPl H w ∧ ∃ B : ValuationSubring N.Om,
      IsPlaceOver (F := H.E) B w ∧ IsFrob (F := H.E) B (normV w) σ} = Set.univ

theorem charpoly_clause_of_chebotarev (hC : Cheb N) (i : N.Loc) (r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i)))
    (hr : GoodR N i r) : At.G1 N i r := by
  have hfin : (placesOver H.E (N.l i) ∪ ↑(N.S i) ∪ ↑(N.Q i) : Set (PlE H)).Finite :=
    ((placesOver_finite H.E (N.l i) (N.lPrime i).out.ne_zero).union (N.S i).finite_toSet).union
      (N.Q i).finite_toSet
  have key := Formalism.IrreducibleCountingLemmas.Z.charpolyCoeffClosure (G H.E N.Om) (N.O i) (N.X i) R.nV
    (fun x g => ((r x g : GL (Fin R.nV) (N.O i)) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)))
    (N.T i).toSubring _ (fun x => (hr x).1) (T_closed N i) (dense_iff_closure_eq.2 (hC _ hfin))
    (by
      rintro g ⟨w, hw, hsp, B, hB, hF⟩ j
      simp only [Set.mem_union, not_or, Finset.mem_coe] at hw
      have h1 : ∀ x, (Matrix.charpolyRev ((r x g : GL (Fin R.nV) (N.O i)) :
          Matrix (Fin R.nV) (Fin R.nV) (N.O i))).coeff j =
          (heckePol N i x w).coeff (revAt R.nV j) := by
        intro x
        have h2 := (hr x).2.2 w ⟨hsp, hw.1.1, hw.1.2, hw.2⟩ B g hB hF
        rw [← Matrix.reverse_charpoly, coeff_reverse, Matrix.charpoly_natDegree_eq_dim, h2,
          Fintype.card_fin]
      show (fun x => _) ∈ N.T i
      simp only [h1]
      exact heckePol_coeff_mem N i w _)
  intro g k
  exact ⟨⟨_, key g k⟩, fun x => rfl⟩

theorem residual_charpoly_of_chebotarev_clause (i : N.Loc) (r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i)))
    (h : At.G1 N i r) (x y : N.X i) (g : G H.E N.Om) :
    ((redRep N i (r x) g : GL (Fin R.nV) (IsLocalRing.ResidueField (N.O i))) :
        Matrix (Fin R.nV) (Fin R.nV) (IsLocalRing.ResidueField (N.O i))).charpoly =
      ((redRep N i (r y) g : GL (Fin R.nV) (IsLocalRing.ResidueField (N.O i))) :
        Matrix (Fin R.nV) (Fin R.nV) (IsLocalRing.ResidueField (N.O i))).charpoly :=
  (Formalism.IrreducibleCountingLemmas.Z.third_reduction_holds (N.O i) (N.X i) (N.T i) (N.T_local i) (G H.E N.Om) R.nV
    (fun x g => ((r x g : GL (Fin R.nV) (N.O i)) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)))
    (fun g j => by
      obtain ⟨f, hf⟩ := h g j
      have : (fun x => (Matrix.charpolyRev ((r x g : GL (Fin R.nV) (N.O i)) :
          Matrix (Fin R.nV) (Fin R.nV) (N.O i))).coeff j) = (f : N.X i → N.O i) := by
        funext x
        exact (hf x).symm
      rw [this]
      exact f.2) x y g).2

end G1

section SS

variable {Γ : Type} [Group Γ] {a : ℕ}

theorem isSSRep_conj {k : Type} [Field k] (ρ ρ' : Γ →* GL (Fin a) k) (Pm : GL (Fin a) k)
    (h : ∀ g, ρ' g = Pm⁻¹ * ρ g * Pm) (hs : IsSSRep ρ) : IsSSRep ρ' := by
  let e : (Fin a → k) ≃ₗ[k] (Fin a → k) :=
    Matrix.toLin'OfInv (M := (Pm : Matrix (Fin a) (Fin a) k))
      (M' := ((Pm⁻¹ : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)) (Units.mul_inv Pm) (Units.inv_mul Pm)
  have he : ∀ v, e v = ((Pm⁻¹ : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).mulVec v := fun v => rfl
  have hes : ∀ v, e.symm v = (Pm : Matrix (Fin a) (Fin a) k).mulVec v := fun v => rfl

  have hint : ∀ g v, e ((ρ g : Matrix (Fin a) (Fin a) k).mulVec v) =
      (ρ' g : Matrix (Fin a) (Fin a) k).mulVec (e v) := by
    intro g v
    rw [he, he, h g]
    simp only [Units.val_mul, Matrix.mulVec_mulVec, mul_assoc]
    rw [Units.mul_inv, mul_one]
  intro W hW
  have hU : IsInv ρ (W.comap (e : (Fin a → k) →ₗ[k] (Fin a → k))) := by
    intro g v hv
    show e _ ∈ W
    rw [hint]
    exact hW g _ hv
  obtain ⟨U', hU', hc⟩ := hs _ hU
  refine ⟨U'.map (e : (Fin a → k) →ₗ[k] (Fin a → k)), ?_, ?_⟩
  · rintro g _ ⟨v, hv, rfl⟩
    exact ⟨_, hU' g v hv, hint g v⟩
  · have h1 := (Submodule.orderIsoMapComap e).isCompl hc
    have h2 : (Submodule.orderIsoMapComap e) (W.comap (e : (Fin a → k) →ₗ[k] (Fin a → k))) = W := by
      show (W.comap (e : (Fin a → k) →ₗ[k] (Fin a → k))).map (e : (Fin a → k) →ₗ[k] (Fin a → k)) = W
      exact Submodule.map_comap_eq_of_surjective e.surjective W
    rw [h2] at h1
    exact h1

variable {K L : Type} [Field K] [Field L] [Algebra K L]

theorem isSSRep_descent (ρ : Γ →* GL (Fin a) K) (hs : IsSSRep (mapRep (algebraMap K L) ρ)) : IsSSRep ρ := by
  obtain ⟨s, hs1⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K L)
    (LinearMap.ker_eq_bot.2 (algebraMap K L).injective)
  have hs2 : ∀ x : K, s (algebraMap K L x) = x := fun x => LinearMap.congr_fun hs1 x
  let ext : (Fin a → K) →ₗ[K] (Fin a → L) := (Algebra.linearMap K L).compLeft (Fin a)
  let res : (Fin a → L) →ₗ[K] (Fin a → K) := s.compLeft (Fin a)
  have hre : ∀ v, res (ext v) = v := fun v => funext fun j => hs2 (v j)
  have hρL : ∀ g, ((mapRep (algebraMap K L) ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) =
      (ρ g : Matrix (Fin a) (Fin a) K).map (algebraMap K L) := fun g => rfl
  have hext : ∀ (M : Matrix (Fin a) (Fin a) K) v, ext (M.mulVec v) = (M.map (algebraMap K L)).mulVec (ext v) := by
    intro M v
    funext j
    exact RingHom.map_mulVec (algebraMap K L) M v j
  have hres : ∀ (M : Matrix (Fin a) (Fin a) K) y, res ((M.map (algebraMap K L)).mulVec y) = M.mulVec (res y) := by
    intro M y
    funext j
    show s (∑ b, algebraMap K L (M j b) * y b) = ∑ b, M j b * s (y b)
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  intro W hW
  let WL : Submodule L (Fin a → L) := Submodule.span L (ext '' W)
  have hWL : IsInv (mapRep (algebraMap K L) ρ) WL := by
    intro g y hy
    have : WL.map ((ρ g : Matrix (Fin a) (Fin a) K).map (algebraMap K L)).mulVecLin ≤ WL := by
      rw [Submodule.map_span_le]
      rintro _ ⟨w, hw, rfl⟩
      rw [Matrix.mulVecLin_apply, ← hext]
      exact Submodule.subset_span ⟨_, hW g w hw, rfl⟩
    exact this ⟨y, hy, rfl⟩
  obtain ⟨WL', hWL', hc⟩ := hs WL hWL
  have hresW : ∀ y ∈ WL, ∀ c : L, res (c • y) ∈ W := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, hw, rfl⟩ := hy
      intro c
      have : res (c • ext w) = s c • w := by
        funext j
        show s (c * algebraMap K L (w j)) = s c * w j
        rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
      rw [this]
      exact W.smul_mem _ hw
    | zero => intro c; simp
    | add y z _ _ hy hz => intro c; rw [smul_add, map_add]; exact W.add_mem (hy c) (hz c)
    | smul d y _ hy => intro c; rw [smul_smul]; exact hy _
  let πL : (Fin a → L) →ₗ[L] (Fin a → L) := WL.subtype ∘ₗ Submodule.projectionOnto WL WL' hc
  have hπmem : ∀ y, πL y ∈ WL := fun y => (Submodule.projectionOnto WL WL' hc y).2
  have hπl : ∀ y ∈ WL, πL y = y := by
    intro y hy
    show ((Submodule.projectionOnto WL WL' hc y : WL) : Fin a → L) = y
    rw [Submodule.projectionOnto_apply_left hc ⟨y, hy⟩]
  have hπr : ∀ y ∈ WL', πL y = 0 := by
    intro y hy
    show ((Submodule.projectionOnto WL WL' hc y : WL) : Fin a → L) = 0
    rw [(Submodule.projectionOnto_apply_eq_zero_iff hc).2 hy]
    rfl
  have hπsub : ∀ y, y - πL y ∈ WL' := by
    intro y
    rw [← Submodule.projectionOnto_apply_eq_zero_iff hc, map_sub, sub_eq_zero]
    apply Subtype.ext
    exact (hπl _ (hπmem y)).symm
  have hπeq : ∀ g y, πL (((ρ g : Matrix (Fin a) (Fin a) K).map (algebraMap K L)).mulVec y) =
      ((ρ g : Matrix (Fin a) (Fin a) K).map (algebraMap K L)).mulVec (πL y) := by
    intro g y
    have h1 : y = πL y + (y - πL y) := by abel
    conv_lhs => rw [h1, Matrix.mulVec_add, map_add]
    have e1 : πL (((ρ g : Matrix (Fin a) (Fin a) K).map (algebraMap K L)).mulVec (πL y)) =
        ((ρ g : Matrix (Fin a) (Fin a) K).map (algebraMap K L)).mulVec (πL y) := hπl _ (hWL g _ (hπmem y))
    have e2 : πL (((ρ g : Matrix (Fin a) (Fin a) K).map (algebraMap K L)).mulVec (y - πL y)) = 0 :=
      hπr _ (hWL' g _ (hπsub y))
    rw [e1, e2, add_zero]
  let p : (Fin a → K) →ₗ[K] (Fin a → K) := res ∘ₗ (πL.restrictScalars K) ∘ₗ ext
  have hpW : ∀ v, p v ∈ W := by
    intro v
    have := hresW _ (hπmem (ext v)) 1
    rwa [one_smul] at this
  have hpid : ∀ w ∈ W, p w = w := by
    intro w hw
    show res (πL (ext w)) = w
    rw [hπl _ (Submodule.subset_span ⟨w, hw, rfl⟩), hre]
  have hpeq : ∀ g v, p ((ρ g : Matrix (Fin a) (Fin a) K).mulVec v) =
      (ρ g : Matrix (Fin a) (Fin a) K).mulVec (p v) := by
    intro g v
    show res (πL (ext _)) = _
    rw [hext, hπeq, hres]
    rfl
  refine ⟨LinearMap.ker p, ?_, ?_⟩
  · intro g v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hpeq, hv, Matrix.mulVec_zero]
  · have := LinearMap.isCompl_of_proj (f := p.codRestrict W hpW) (fun x => Subtype.ext (hpid x x.2))
    rwa [LinearMap.ker_codRestrict] at this

end SS

section Cont

theorem continuous_of_comp {O : Type} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] {J : Ideal O}
    (hJ : IsAdic J) {L : Type} [NormedField L] (ι : O →+* L)
    (hε : ∀ n : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ x, ‖ι x‖ < ε → x ∈ J ^ n)
    {X : Type} [TopologicalSpace X] (f : X → O) (hf : Continuous (fun x => ι (f x))) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x0 s hs
  have h0 : (fun y => y + f x0) ⁻¹' s ∈ 𝓝 (0 : O) :=
    (continuous_add_right (f x0)).continuousAt.preimage_mem_nhds (by simpa using hs)
  obtain ⟨n, hn⟩ := (isAdic_iff.1 hJ).2 _ h0
  obtain ⟨ε, hε0, hε⟩ := hε n
  have hU : {x | ‖ι (f x) - ι (f x0)‖ < ε} ∈ 𝓝 x0 := by
    have hc : Continuous fun x => ‖ι (f x) - ι (f x0)‖ := (hf.sub continuous_const).norm
    exact (isOpen_lt hc continuous_const).mem_nhds (by simpa using hε0)
  rw [Filter.mem_map]
  filter_upwards [hU] with x hx
  have h1 : f x - f x0 ∈ J ^ n := hε _ (by rw [map_sub]; exact hx)
  have h2 := hn h1
  simpa using h2

theorem norm_le_one_of_finite {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
    [Module.Finite ℤ_[l] O] {L : Type} [NormedField L] (ι : O →+* L)
    (hz : ∀ z : ℤ_[l], ‖ι (algebraMap ℤ_[l] O z)‖ ≤ 1) (y : O) : ‖ι y‖ ≤ 1 := by
  obtain ⟨n, b, hb⟩ := Module.Finite.exists_fin (R := ℤ_[l]) (M := O)
  have hbd : ∀ x : O, ‖ι x‖ ≤ ∑ j, ‖ι (b j)‖ := by
    intro x
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[l]).1 (hb ▸ Submodule.mem_top : x ∈ _)
    rw [map_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [Algebra.smul_def, map_mul, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hz _)
  by_contra hcon
  push Not at hcon
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (∑ j, ‖ι (b j)‖) hcon
  have := hbd (y ^ k)
  rw [map_pow, norm_pow] at this
  exact absurd hk (not_lt.2 this)

theorem mem_pow_of_norm_lt {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] {L : Type} [NormedField L]
    (ι : O →+* L) (hinj : Function.Injective ι) (hz : ∀ z : ℤ_[l], ‖ι (algebraMap ℤ_[l] O z)‖ ≤ 1) (n : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x, ‖ι x‖ < ε → x ∈ IsLocalRing.maximalIdeal O ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have h1 := norm_le_one_of_finite ι hz
  have hc0 : 0 < ‖ι ϖ‖ := norm_pos_iff.2 (fun h => hϖ.ne_zero (hinj (h.trans (map_zero ι).symm)))
  have hu : ∀ u : Oˣ, ‖ι u‖ = 1 := by
    intro u
    refine le_antisymm (h1 _) ?_
    have h2 : ‖ι u‖ * ‖ι (u⁻¹ : Oˣ)‖ = 1 := by
      rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
    by_contra hlt
    push Not at hlt
    have h3 : ‖ι u‖ * ‖ι (u⁻¹ : Oˣ)‖ < 1 :=
      (mul_le_of_le_one_right (norm_nonneg _) (h1 _)).trans_lt hlt
    exact absurd h2 (ne_of_lt h3)
  refine ⟨‖ι ϖ‖ ^ n, pow_pos hc0 n, fun x hx => ?_⟩
  by_cases hx0 : x = 0
  · rw [hx0]; exact Ideal.zero_mem _
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  rw [map_mul, norm_mul, hu, one_mul, map_pow, norm_pow] at hx
  have hkn : n ≤ k := by
    by_contra hlt
    push Not at hlt
    exact absurd hx (not_lt.2 (pow_le_pow_of_le_one hc0.le (h1 ϖ) hlt.le))
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  refine Ideal.mul_mem_left _ _ ?_
  rw [Ideal.mem_span_singleton]
  exact pow_dvd_pow _ hkn

end Cont

section Main

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem iotaOQ_injective (i : N.Loc) : Function.Injective (iotaOQ N A i) :=
  (A.iotaQ i).injective.comp (IsFractionRing.injective (N.O i) (FractionRing (N.O i)))

theorem iotaOQ_norm_int (i : N.Loc) (z : ℤ_[N.l i]) :
    ‖iotaOQ N A i (algebraMap ℤ_[N.l i] (N.O i) z)‖ ≤ 1 := by
  have : iotaOQ N A i (algebraMap ℤ_[N.l i] (N.O i) z) =
      algebraMap ℚ_[N.l i] (Qbar (N.l i)) (z : ℚ_[N.l i]) := A.iotaQ_alg i z
  rw [this, norm_algebraMap']
  exact PadicInt.norm_le_one z

theorem isHeckeGalois_of_conj (i : N.Loc) (x : N.X i) (ρ : G H.E N.Om →* GL (Fin R.nV) (Qbar (N.l i)))
    (hρ : At.IsHeckeGaloisQ N A i x ρ) (r : G H.E N.Om →* GL (Fin R.nV) (N.O i))
    (Pm : GL (Fin R.nV) (Qbar (N.l i))) (h : ∀ g, mapRep (iotaOQ N A i) r g = Pm⁻¹ * ρ g * Pm) :
    IsHeckeGalois N i x r := by
  obtain ⟨hc, hss, hF⟩ := hρ
  have hmat : ∀ g, ((r g : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)).map (iotaOQ N A i) =
      ((Pm⁻¹ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i))) *
        ((ρ g : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i))) *
        (Pm : Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i))) := fun g => congrArg Units.val (h g)
  refine ⟨?_, ?_, ?_⟩
  ·
    have hcm : Continuous fun g => ((r g : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)).map (iotaOQ N A i) := by
      simp only [hmat]
      exact (continuous_const.matrix_mul hc).matrix_mul continuous_const
    refine continuous_matrix fun a b => ?_
    refine continuous_of_comp (N.O_adic i) (iotaOQ N A i)
      (mem_pow_of_norm_lt (iotaOQ N A i) (iotaOQ_injective N A i) (iotaOQ_norm_int N A i)) _ ?_
    exact (continuous_apply b).comp ((continuous_apply a).comp hcm)
  ·
    have h1 : IsSSRep (mapRep (iotaOQ N A i) r) := isSSRep_conj ρ _ Pm h hss
    letI : Algebra (Kf N i) (Qbar (N.l i)) := (A.iotaQ i).toAlgebra
    exact isSSRep_descent (L := Qbar (N.l i)) (mapRep (algebraMap (N.O i) (Kf N i)) r) h1
  ·
    intro w hw B σ hB hσ
    apply Polynomial.map_injective _ (iotaOQ_injective N A i)
    rw [← hF w hw B σ hB hσ, ← Matrix.charpoly_map, hmat]
    have h2 := Matrix.charpoly_units_conj (Pm⁻¹ : GL (Fin R.nV) (Qbar (N.l i)))
      ((ρ σ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i)))
    rwa [← Matrix.coe_units_inv, inv_inv] at h2

theorem exists_GoodR (hO : At.OLarge N A) (i : N.Loc)
    (h : ∃ rq : N.X i → (G H.E N.Om →* GL (Fin R.nV) (Qbar (N.l i))), ∀ x, At.IsHeckeGaloisQ N A i x (rq x)) :
    ∃ r, GoodR N i r := by
  obtain ⟨rq, hq⟩ := h
  choose r Pm hr using fun x => hO i x (rq x) (hq x)
  exact ⟨r, fun x => isHeckeGalois_of_conj N A i x (rq x) (hq x) (r x) (Pm x) (hr x)⟩

end Main

section C42

theorem list_prod_fin {M α : Type} [CommMonoid M] (l : List α) (F : α → M) :
    (l.map F).prod = ∏ j : Fin l.length, F (l.get j) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, ih]
    exact (Fin.prod_univ_succ (fun j : Fin (l.length + 1) => F ((a :: l).get j))).symm

theorem list_sum_fin {M α : Type} [AddCommMonoid M] (l : List α) (F : α → M) :
    (l.map F).sum = ∑ j : Fin l.length, F (l.get j) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih]
    exact (Fin.sum_univ_succ (fun j : Fin (l.length + 1) => F ((a :: l).get j))).symm

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

namespace At

def TieLab : Prop :=
  (∀ (k : Fin 2) (v : N.PlG k) (a : A.LP (A.plGw k v)) (s : ℝ),
    A.items₂ k (A.plGw k v) (A.lpTw a s) = A.items₂ k (A.plGw k v) a) ∧
  ∀ (k : Fin 2) (v : N.PlG k) (a : A.LP (A.plGw k v)), (A.items₂ k (A.plGw k v) a).natDegree ≤ A.lpDim a

end At

theorem inertiaCharpoly_speh_eq_pow (hT : At.TieLab N A) (k : Fin 2) (v : N.PlG k) (p : Part A.CG) :
    A.items₂ k (A.plGw k v) (spehLoc N A p (A.plGw k v)) =
      A.items₂ k (A.plGw k v) (A.locG p.π (A.plGw k v)) ^ p.d := by
  have key : ∀ l : List ℝ, A.items₂ k (A.plGw k v) (l.foldr
      (fun (m : ℝ) acc => A.lpSum (A.lpTw (A.locG p.π (A.plGw k v)) (((p.d : ℝ) - 1) / 2 - m)) acc)
        (A.lpZero (A.plGw k v))) = A.items₂ k (A.plGw k v) (A.locG p.π (A.plGw k v)) ^ l.length := by
    intro l
    induction l with
    | nil => simp [A.inertiaCharpoly_zero]
    | cons a l ih => simp only [List.foldr_cons, A.inertiaCharpoly_add, hT.1, ih, List.length_cons, pow_succ']
  unfold spehLoc
  rw [key]
  congr 1
  simp

theorem inertiaCharpoly_eq_of_iso (hT : At.TieLab N A) (k : Fin 2) (v : N.PlG k) (Sig : List (Part A.CG)) :
    A.items₂ k (A.plGw k v) (isoLoc N A Sig (A.plGw k v)) =
      (Sig.map fun p => A.items₂ k (A.plGw k v) (A.locG p.π (A.plGw k v)) ^ p.d).prod := by
  induction Sig with
  | nil => simp [isoLoc, A.inertiaCharpoly_zero]
  | cons p l ih =>
    have : isoLoc N A (p :: l) (A.plGw k v) =
        A.lpSum (spehLoc N A p (A.plGw k v)) (isoLoc N A l (A.plGw k v)) := rfl
    rw [this, A.inertiaCharpoly_add, inertiaCharpoly_speh_eq_pow N A hT, ih, List.map_cons, List.prod_cons]

theorem not_over_of_ne {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) {w : HeightOneSpectrum (𝓞 E)} (hw : w ∈ placesOver E p) : w ∉ placesOver E q := by
  intro hw'
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have h1 : ((a : 𝓞 E)) * ((p : ℕ) : 𝓞 E) + (b : 𝓞 E) * ((q : ℕ) : 𝓞 E) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hab
  rw [← h1]
  exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hw) (w.asIdeal.mul_mem_left _ hw')

theorem plGw_split (i : N.Loc) (k : Fin 2) (hk : H.g k ≠ N.l i) (v : N.PlG k) :
    IsSplitPl H (A.plGw k v) := by
  refine N.SQ_split i _ (Or.inl ((N.S_def i _).2 ⟨?_, ?_⟩))
  · have := A.plGw_over k v
    fin_cases k
    · exact Or.inl this
    · exact Or.inr (Or.inl this)
  · exact not_over_of_ne (H.g_prime k) (N.lPrime i).out hk (A.plGw_over k v)

theorem parameter_of_good_is_cuspidal (hT : At.TieLab N A) (i : N.Loc) (σ : what₂.FT) (hg : N.goodRow σ)
    (Sig : List (Part A.CG)) (hS : HasParamW N A i σ Sig) : IsCuspIso N A Sig := by
  obtain ⟨k, hk⟩ : ∃ k : Fin 2, H.g k ≠ N.l i := by
    by_cases h0 : H.g 0 = N.l i
    · exact ⟨1, fun h1 => H.g_ne (h0.trans h1.symm)⟩
    · exact ⟨0, h0⟩
  have : Fact (H.g k).Prime := ⟨H.g_prime k⟩
  obtain ⟨h1, h2, -, -, h5, -⟩ := (hg k).1
  obtain ⟨hpos, hrank, hloc⟩ := hS
  have : Nonempty (N.PlG k) := by
    rw [← Fintype.card_pos_iff, N.card_PlG k]
    show 0 < 2 * R.ord
    have := R.ord_pos
    omega
  have hr : 1 ≤ R.r := by
    have := R.two_le_m
    show 1 ≤ R.k + R.m - 1
    omega

  have hf : ∀ v, N.lab k σ v = ∏ j : Fin Sig.length,
      A.items₂ k (A.plGw k v) (A.locG (Sig.get j).π (A.plGw k v)) ^ (Sig.get j).d := by
    intro v
    rw [A.lab_loc i k σ v, ← hloc _ (plGw_split N A i k hk v), inertiaCharpoly_eq_of_iso N A hT,
      list_prod_fin Sig (fun p => A.items₂ k (A.plGw k v) (A.locG p.π (A.plGw k v)) ^ p.d)]
  have hrk : ∑ j : Fin Sig.length, (Sig.get j).a * (Sig.get j).d = R.r := by
    rw [← hrank, rankIso, list_sum_fin Sig (fun p => p.a * p.d)]
  have hd : ∀ j : Fin Sig.length, 1 ≤ (Sig.get j).a ∧ 1 ≤ (Sig.get j).d :=
    fun j => hpos _ (List.get_mem Sig j)

  have hdeg : ∀ v (j : Fin Sig.length),
      (A.items₂ k (A.plGw k v) (A.locG (Sig.get j).π (A.plGw k v))).natDegree = (Sig.get j).a := by
    intro v
    have hne : ∀ j ∈ (Finset.univ : Finset (Fin Sig.length)),
        A.items₂ k (A.plGw k v) (A.locG (Sig.get j).π (A.plGw k v)) ^ (Sig.get j).d ≠ 0 := by
      rw [← Finset.prod_ne_zero_iff, ← hf v]
      exact (h1 v).1.ne_zero
    have hsum : ∑ j : Fin Sig.length,
        (A.items₂ k (A.plGw k v) (A.locG (Sig.get j).π (A.plGw k v))).natDegree * (Sig.get j).d =
        ∑ j : Fin Sig.length, (Sig.get j).a * (Sig.get j).d := by
      rw [hrk, ← (h1 v).2.1, hf v, natDegree_prod _ _ hne]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [natDegree_pow, mul_comm]
    have hle : ∀ j ∈ (Finset.univ : Finset (Fin Sig.length)),
        (A.items₂ k (A.plGw k v) (A.locG (Sig.get j).π (A.plGw k v))).natDegree * (Sig.get j).d ≤
        (Sig.get j).a * (Sig.get j).d := by
      intro j _
      refine Nat.mul_le_mul_right _ ?_
      have := hT.2 k v (A.locG (Sig.get j).π (A.plGw k v))
      rwa [A.locG_dim] at this
    intro j
    have := (Finset.sum_eq_sum_iff_of_le hle).1 hsum j (Finset.mem_univ j)
    exact Nat.eq_of_mul_eq_mul_right (hd j).2 this
  obtain ⟨hc, hall⟩ := Formalism.IrreducibleCountingLemmas.Z.good_cuspidal_multiplicity_one (ZMod (H.g k)) (N.PlG k) R.r (N.lab k σ)
    (Fin Sig.length) (fun j => (Sig.get j).a) (fun j => (Sig.get j).d)
    (fun v j => A.items₂ k (A.plGw k v) (A.locG (Sig.get j).π (A.plGw k v))) hr
    (fun v => (h1 v).2.1) h2 hf hdeg (fun j => (hd j).1) (fun j => (hd j).2)
    (by
      rintro ⟨a, ha1, ha2, ha⟩
      obtain ⟨v, hv⟩ := h5 a ha1 ha2
      exact hv (ha v))
  rw [Fintype.card_fin] at hc
  obtain ⟨p, rfl⟩ := List.length_eq_one_iff.1 hc
  obtain ⟨hd1, ha1⟩ := hall ⟨0, by simp⟩
  obtain ⟨a, π, d⟩ := p
  simp only [List.get_eq_getElem, List.getElem_cons_zero] at hd1 ha1
  subst hd1 ha1
  exact ⟨π, rfl⟩

namespace At

def ReducedParameterProposition (i : N.Loc) : Prop :=
  ∀ σ, what₂.isot (N.j i) σ ≠ ⊥ →
    ((∃ lam : ℝ, 0 < lam ∧ ∀ f ∈ what₂.isot (N.j i) σ,
        what₂.thetaP (N.mu i) (N.j i) (what₂.thetaT (N.mu i) (N.j i) f) = (lam : ℂ) • f) ∧
      ∃ P, thetaOf N A i σ P) ∧
    (∃ Sig, HasParamW N A i σ Sig ∧
      ∀ P, thetaOf N A i σ P → IsBCV N A i P (twistIso N A (Sig ++ [muPart N A i]) A.etaTinv))

end At

theorem parameter_proposition_iff (hT : At.TieLab N A) (i : N.Loc) : At.Conclusion42 N A i ↔ At.ReducedParameterProposition N A i :=
  ⟨fun h σ hσ => ⟨(h σ hσ).1, (h σ hσ).2.1⟩,
    fun h σ hσ => ⟨(h σ hσ).1, (h σ hσ).2, fun hg Sig hS => parameter_of_good_is_cuspidal N A hT i σ hg Sig hS⟩⟩

end C42

section Del

theorem eq_one_of_map_eq_one {A B : Type} [CommRing A] [IsDomain A] [CommRing B] (f : A →+* B) (n : ℕ)
    (hn : ((n : ℕ) : B) ≠ 0) (x : A) (hx : x ^ n = 1) (hf : f x = 1) : x = 1 := by
  by_contra h
  have h1 : (x - 1) * ∑ k ∈ Finset.range n, x ^ k = 0 := by rw [mul_geom_sum, hx, sub_self]
  have h2 : ∑ k ∈ Finset.range n, x ^ k = 0 := (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 h)
  apply hn
  have h3 := congrArg f h2
  simpa [map_sum, map_pow, hf] using h3

theorem card_map_eq {Γ A B : Type} [Group Γ] [Group A] [Group B] (K : Subgroup Γ) (δ : Γ →* A) (χ : Γ →* B)
    (φ : A →* B) (h : ∀ σ ∈ K, χ σ = φ (δ σ)) (hinj : ∀ x ∈ K.map δ, φ x = 1 → x = 1) :
    Nat.card (K.map χ) = Nat.card (K.map δ) := by
  have e : K.map χ = (K.map δ).map φ := by
    ext b
    simp only [Subgroup.mem_map, exists_exists_and_eq_and]
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      exact ⟨σ, hσ, (h σ hσ).symm⟩
    · rintro ⟨σ, hσ, rfl⟩
      exact ⟨σ, hσ, h σ hσ⟩
  rw [e]
  have hI : Set.InjOn φ (K.map δ : Set A) := by
    intro a ha b hb hab
    have h1 : φ (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 := hinj _ ((K.map δ).mul_mem ha ((K.map δ).inv_mem hb)) h1
    exact mul_inv_eq_one.1 h2
  exact Nat.card_image_of_injOn hI

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)

theorem natCast_ne_zero_O (i : N.Loc) (n : ℕ) (hn : n ≠ 0) : ((n : ℕ) : N.O i) ≠ 0 := by
  intro h
  have h1 : ((n : ℕ) : what₂.LL) ≠ 0 := by
    intro h0
    have h2 := congrArg what₂.embLL h0
    rw [map_natCast, map_zero] at h2
    exact hn (by exact_mod_cast h2)
  have h3 : N.embK i ((n : ℕ) : what₂.LL) = 0 := by
    rw [map_natCast, ← map_natCast (algebraMap (N.O i) (FractionRing (N.O i))), h, map_zero]
  exact h1 ((map_eq_zero (N.embK i)).mp h3)

end Del

theorem Del_holds (D : D7) (i : D.nd.Loc) : At.Del D.nd i := by
  intro w hS hw
  have hpD : w ∈ D.ntw.pD (D.ntw.twOf i) := by
    have : w ∈ (D.ntw.pD (D.ntw.twOf i) : Set (HeightOneSpectrum (𝓞 D.host.E))) := by
      rw [D.ntw.pD_eq, D.ntw.twOf_l]
      exact hw
    exact this
  have hQ : w ∉ D.nd.Q i := Finset.disjoint_left.1 (D.nd.SQ_disj i) hS
  have hpl := D.nd.plOm.2 w
  have hψ : ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), D.ntw.psiL i σ = 1 := by
    intro σ hσ
    by_contra h
    exact hQ ((D.ntw.psiL_ram i w _ hpl).1 ⟨σ, hσ, h⟩)
  have h15 := D.ntw.delta_15 (D.ntw.twOf i) w hpD _ hpl
  rw [← h15]
  have hpow : ∀ x ∈ (Ine (F := D.host.E) (D.nd.plOm.1 w)).map (D.ntw.delta (D.ntw.twOf i)), x ^ 15 = 1 := by
    intro x hx
    have h := pow_card_eq_one'
      (G := (Ine (F := D.host.E) (D.nd.plOm.1 w)).map (D.ntw.delta (D.ntw.twOf i))) (x := ⟨x, hx⟩)
    rw [h15] at h
    exact congrArg Subtype.val h
  have hone : ∀ y : (D.ntw.O0 (D.ntw.twOf i))ˣ, y ^ 15 = 1 →
      Units.map (D.ntw.twist₂ i).toMonoidHom y = 1 → y = 1 := by
    intro y hy h
    apply Units.ext
    refine eq_one_of_map_eq_one (D.ntw.twist₂ i) 15 (natCast_ne_zero_O D.nd i 15 (by norm_num)) _ ?_
      (congrArg Units.val h)
    rw [← Units.val_pow_eq_pow_val, hy, Units.val_one]
  have hχ : ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), D.nd.chi i 1 σ =
      Units.map (D.ntw.twist₂ i).toMonoidHom (D.ntw.chi1 (D.ntw.twOf i) (D.nd.j i) (D.ntw.twSide i) σ) := by
    intro σ hσ
    rw [D.ntw.chi_tw i]
    simp [hψ σ hσ]
  cases hs : D.ntw.twSide i
  · refine card_map_eq _ (D.ntw.delta (D.ntw.twOf i)) (D.nd.chi i 1)
      ((Units.map (D.ntw.twist₂ i).toMonoidHom).comp invMonoidHom) (fun σ hσ => ?_) (fun x hx h => ?_)
    · rw [hχ σ hσ, D.ntw.twistCharacterFamily_at_auxiliaryPlaces _ _ _ w hpD _ hpl σ hσ, hs]
      simp
    · have h1 := hone x⁻¹ (by rw [inv_pow, hpow x hx, inv_one]) h
      exact inv_eq_one.1 h1
  · refine card_map_eq _ (D.ntw.delta (D.ntw.twOf i)) (D.nd.chi i 1)
      (Units.map (D.ntw.twist₂ i).toMonoidHom) (fun σ hσ => ?_) (fun x hx h => hone x (hpow x hx) h)
    rw [hχ σ hσ, D.ntw.twistCharacterFamily_at_auxiliaryPlaces _ _ _ w hpD _ hpl σ hσ, hs]
    simp

section G5c

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) {ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))}
  {π : N.X i} {S : IdempotentChoiceData N i}

theorem inR'_one : InR' N r S 1 :=
  ⟨1, fun _ => 1, fun _ => 1, fun _ => S.T'.one_mem, by funext x'; simp⟩

theorem inY_yg (γ : GE N) : InY N r S (yg N r S γ) :=
  ⟨1, fun _ => 1, fun _ => γ, fun _ => inR'_one N r, by simp⟩

theorem phi_yg_zero (c : Fin R.t) (φ : (S.X' → MatN N i) →ₗ[N.O i] KmodO (N.O i))
    (hφ : ∀ a, InR' N r S a → ∀ y, InY N r S y → φ (a * y) = S.ψχ c a • φ y) (γ : GE N)
    (a : S.X' → MatN N i) (ha : InR' N r S a) (hz : a * yg N r S γ = 0) (hu : IsUnit (S.ψχ c a)) :
    φ (yg N r S γ) = 0 := by
  have h := hφ a ha _ (inY_yg N r γ)
  rw [hz, map_zero] at h
  exact (hu.smul_eq_zero).1 h.symm

theorem psiChi_span (hG : Formalism.MainNotions.SumRepresentations.At.IdempotentChoiceProperties N r ρ π S) (c : Fin R.t) {m : ℕ} (f : Fin m → N.X i → N.O i)
    (hf : ∀ k, f k ∈ N.T i) (g : Fin m → GE N) :
    InR' N r S (fun x' => ∑ k, f k (S.p x') • rO N i r (S.p x') (g k)) ∧
    S.ψχ c (fun x' => ∑ k, f k (S.p x') • rO N i r (S.p x') (g k)) =
      ∑ k, f k π * ((chiU N i ((c : ℕ) + 1) (g k) : (N.O i)ˣ) : N.O i) := by
  obtain ⟨-, hgrp, hact, -, -, -, ⟨hT, -⟩, -, ⟨hπ, -⟩, -⟩ := hG
  have hIn : InR' N r S (fun x' => ∑ k, f k (S.p x') • rO N i r (S.p x') (g k)) :=
    ⟨m, fun k x' => f k (S.p x'), g, fun k => hT _ (hf k), by funext x'; simp [Finset.sum_apply]⟩
  refine ⟨hIn, ?_⟩
  have h1 := hact _ hIn (S.e.symm ((0 : Fin R.r → KK N i), Pi.single c (1 : KK N i)))
  beta_reduce at h1
  rw [hπ] at h1
  have hM : (∑ k, f k π • rO N i r π (g k)).map (toK N i) =
      ∑ k, toK N i (f k π) • mapM (toK N i) (rO N i r π) (g k) := by
    show (toK N i).mapMatrix _ = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ext a b
    simp [mapM]
  rw [hM, Matrix.sum_mulVec, map_sum] at h1
  simp only [Matrix.smul_mulVec, map_smul, hgrp] at h1
  have h2 := congrFun (congrArg Prod.snd h1) c
  simp only [LinearEquiv.apply_symm_apply, Pi.single_eq_same, mul_one, Prod.snd_sum, Prod.smul_snd,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
  apply IsFractionRing.injective (N.O i) (KK N i)
  rw [← h2, map_sum]
  simp

end G5c

section Quad

theorem quad_of_diag {K : Type} [Field K] {n : ℕ} (P : GL (Fin n) K) (M M' : Matrix (Fin n) (Fin n) K)
    (d d' : Fin n → K) (c : K)
    (h : ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M * (P : Matrix (Fin n) (Fin n) K) =
      Matrix.diagonal d)
    (h' : ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M' * (P : Matrix (Fin n) (Fin n) K) =
      Matrix.diagonal d')
    (hz : ∀ k, (d' k - 1) * (d k - c) = 0) : (M' - 1) * (M - c • (1 : Matrix (Fin n) (Fin n) K)) = 0 := by
  have e1 : (P : Matrix (Fin n) (Fin n) K) * ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 :=
    Units.mul_inv P
  have e2 : ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (P : Matrix (Fin n) (Fin n) K) = 1 :=
    Units.inv_mul P
  have hA : ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (M' - 1) * (P : Matrix (Fin n) (Fin n) K) =
      Matrix.diagonal (fun k => d' k - 1) := by
    rw [mul_sub, sub_mul, h', mul_one, e2, ← Matrix.diagonal_one, Matrix.diagonal_sub]
  have hB : ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (M - c • (1 : Matrix (Fin n) (Fin n) K)) *
      (P : Matrix (Fin n) (Fin n) K) = Matrix.diagonal (fun k => d k - c) := by
    rw [mul_sub, sub_mul, h, Matrix.mul_smul, Matrix.smul_mul, mul_one, e2, Matrix.smul_one_eq_diagonal,
      Matrix.diagonal_sub]
  have hAB : ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((M' - 1) * (M - c • (1 : Matrix (Fin n) (Fin n) K))) * (P : Matrix (Fin n) (Fin n) K) = 0 := by
    have : ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((M' - 1) * (M - c • (1 : Matrix (Fin n) (Fin n) K))) * (P : Matrix (Fin n) (Fin n) K) =
        (((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (M' - 1) * (P : Matrix (Fin n) (Fin n) K)) *
        (((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (M - c • (1 : Matrix (Fin n) (Fin n) K)) *
          (P : Matrix (Fin n) (Fin n) K)) := by
      calc _ = ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (M' - 1) * 1 *
            (M - c • (1 : Matrix (Fin n) (Fin n) K)) * (P : Matrix (Fin n) (Fin n) K) := by
            simp only [mul_one, mul_assoc]
        _ = _ := by rw [← e1]; simp only [mul_assoc]
    rw [this, hA, hB, Matrix.diagonal_mul_diagonal]
    simp [hz]
  calc (M' - 1) * (M - c • (1 : Matrix (Fin n) (Fin n) K))
      = (P : Matrix (Fin n) (Fin n) K) * (((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((M' - 1) * (M - c • (1 : Matrix (Fin n) (Fin n) K))) * (P : Matrix (Fin n) (Fin n) K)) *
        ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        rw [← mul_assoc, ← mul_assoc, e1, one_mul, mul_assoc, e1, mul_one]
    _ = 0 := by rw [hAB]; simp

end Quad

section G5c

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) {ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))}
  {π : N.X i} {S : IdempotentChoiceData N i}

def SplitI (w : PlE H) (x : N.X i) : Prop :=
  ∃ Pm : GL (Fin R.nV) (Kf N i), ∀ γ ∈ Ine (F := H.E) (N.plOm.1 w),
    ((Pm⁻¹ * mapRep (algebraMap (N.O i) (Kf N i)) (r x) γ * Pm : GL _ _) :
      Matrix (Fin R.nV) (Fin R.nV) (Kf N i)) =
    Matrix.diagonal (fun k : Fin R.nV => if (k : ℕ) < R.r then 1 else algebraMap (N.O i) (Kf N i) (chi1 N i γ))

theorem quad_of_split {w : PlE H} {x : N.X i} (h : SplitI N r w x) (γ' γ : GE N)
    (hγ' : γ' ∈ Ine (F := H.E) (N.plOm.1 w)) (hγ : γ ∈ Ine (F := H.E) (N.plOm.1 w)) :
    (((r x γ' : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)) - 1) *
      (((r x γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)) - chi1 N i γ • 1) = 0 := by
  obtain ⟨Pm, hP⟩ := h
  have h1 := quad_of_diag Pm
    (((r x γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)).map (algebraMap (N.O i) (Kf N i)))
    (((r x γ' : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)).map (algebraMap (N.O i) (Kf N i)))
    _ _ (algebraMap (N.O i) (Kf N i) (chi1 N i γ)) (hP γ hγ) (hP γ' hγ') (fun k => by
      split_ifs <;> simp)
  apply Matrix.map_injective (IsFractionRing.injective (N.O i) (Kf N i))
  show (algebraMap (N.O i) (Kf N i)).mapMatrix _ = (algebraMap (N.O i) (Kf N i)).mapMatrix 0
  rw [map_mul, map_sub, map_sub, map_one, map_zero]
  have h3 : (algebraMap (N.O i) (Kf N i)).mapMatrix (chi1 N i γ • (1 : Matrix (Fin R.nV) (Fin R.nV) (N.O i))) =
      algebraMap (N.O i) (Kf N i) (chi1 N i γ) • 1 := by
    ext a b
    by_cases hab : a = b <;> simp [hab, Matrix.one_apply]
  rw [h3]
  exact h1

theorem cycZ_one_of_Ine (w : PlE H) (hw : w ∉ placesOver H.E (N.l i)) (g : GE N)
    (hg : g ∈ Ine (F := H.E) (N.plOm.1 w)) : cycZ (F := H.E) (Ω := N.Om) (N.l i) g = 1 := by
  refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
  rw [cycZ_toZModPow_eq (v := w) hw (N.plOm.2 w) (q := 1) (fun x hx => by simpa using hg.2 x hx) n]
  simp

theorem character_eq_first_off_l (w : PlE H) (hw : w ∉ placesOver H.E (N.l i)) (c : ℕ) (h1 : 1 ≤ c) (h2 : c ≤ R.t)
    (g : GE N) (hg : g ∈ Ine (F := H.E) (N.plOm.1 w)) : N.chi i c g = N.chi i 1 g := by
  rw [N.chi_def i c h1 h2]
  simp [cycZ_one_of_Ine N w hw g hg]

theorem yg_eq (γ : GE N) (x' : S.X') :
    yg N r S γ x' = (((chiU N i 1 γ)⁻¹ : (N.O i)ˣ) : N.O i) •
      ((((r (S.p x') γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)) - chi1 N i γ • 1) * Eel N S x') := by
  have : (((chiU N i 1 γ)⁻¹ : (N.O i)ˣ) : N.O i) * chi1 N i γ = 1 := Units.inv_mul _
  rw [sub_mul, smul_sub, smul_mul_assoc, one_mul, smul_smul, this, one_smul]
  rfl

end G5c

section G5c

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) {ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))}
  {π : N.X i} {S : IdempotentChoiceData N i}

theorem Y_of_b (hG : Formalism.MainNotions.SumRepresentations.At.IdempotentChoiceProperties N r ρ π S) (w : PlE H) (hw : w ∉ placesOver H.E (N.l i))
    (Pp : Polynomial (N.T i))
    (hu : IsUnit (Pp.eval (algebraMap (N.O i) (N.T i) (chi1 N i (N.gam0 i w)))))
    (hk : ∀ x, ∀ γ ∈ Ine (F := H.E) (N.plOm.1 w),
      Polynomial.aeval ((r x (N.gam0 i w) : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i))
          (Pp.map ((Pi.evalRingHom (fun _ : N.X i => N.O i) x).comp (N.T i).val.toRingHom)) *
        (((r x γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)) - chi1 N i γ • 1) = 0)
    (c : Fin R.t) (φ : (S.X' → MatN N i) →ₗ[N.O i] KmodO (N.O i))
    (hφ : ∀ a, InR' N r S a → ∀ y, InY N r S y → φ (a * y) = S.ψχ c a • φ y)
    (γ : GE N) (hγ : γ ∈ Ine (F := H.E) (N.plOm.1 w)) : φ (yg N r S γ) = 0 := by
  obtain ⟨hIn, hψ⟩ := psiChi_span N r hG c (m := Pp.natDegree + 1)
    (fun k => (Pp.coeff k : N.X i → N.O i)) (fun k => (Pp.coeff k).2) (fun k => N.gam0 i w ^ (k : ℕ))
  have haev : ∀ x, ∑ k : Fin (Pp.natDegree + 1), (Pp.coeff k : N.X i → N.O i) x •
      rO N i r x (N.gam0 i w ^ (k : ℕ)) =
      Polynomial.aeval ((r x (N.gam0 i w) : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i))
          (Pp.map ((Pi.evalRingHom (fun _ : N.X i => N.O i) x).comp (N.T i).val.toRingHom)) := by
    intro x
    rw [aeval_eq_sum_range' (n := Pp.natDegree + 1) (Nat.lt_succ_of_le natDegree_map_le),
      Finset.sum_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [coeff_map, map_pow]
    rfl
  refine phi_yg_zero N r c φ hφ γ _ hIn ?_ ?_
  · funext x'
    show (∑ k : Fin (Pp.natDegree + 1), (Pp.coeff k : N.X i → N.O i) (S.p x') •
      rO N i r (S.p x') (N.gam0 i w ^ (k : ℕ))) * yg N r S γ x' = 0
    rw [haev, yg_eq, mul_smul_comm, ← mul_assoc, hk _ γ hγ, zero_mul, smul_zero]
  · rw [hψ]
    have h1 := hu.map ((Pi.evalRingHom (fun _ : N.X i => N.O i) π).comp (N.T i).val.toRingHom)
    rw [eval_eq_sum_range, map_sum, Finset.sum_range] at h1
    convert h1 using 2
    rw [map_mul, map_pow, map_pow, character_eq_first_off_l N w hw _ (by omega) (by have := c.2; omega) _ (N.locNd_chebotarevPlace_mem i w)]
    simp [chi1]

theorem exists_unit_of_card (w : PlE H)
    (h15 : Nat.card ((Ine (F := H.E) (N.plOm.1 w)).map (N.chi i 1)) = 15) :
    ∃ γ' ∈ Ine (F := H.E) (N.plOm.1 w), IsUnit (chi1 N i γ' - 1) := by
  have : Finite ((Ine (F := H.E) (N.plOm.1 w)).map (N.chi i 1)) :=
    Nat.finite_of_card_ne_zero (by rw [h15]; norm_num)
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := (Ine (F := H.E) (N.plOm.1 w)).map (N.chi i 1))
  have ho : orderOf ζ = 15 := by rw [orderOf_eq_card_of_forall_mem_zpowers hζ, h15]
  have hp : IsPrimitiveRoot (((ζ : (N.O i)ˣ)) : N.O i) 15 := by
    rw [IsPrimitiveRoot.coe_units_iff, IsPrimitiveRoot.coe_submonoidClass_iff, ← ho]
    exact IsPrimitiveRoot.orderOf ζ
  obtain ⟨γ', hγ', he⟩ := ζ.2
  refine ⟨γ', hγ', ?_⟩
  have := Formalism.IrreducibleCountingLemmas.Z.phi15_is_unit_holds (N.O i) _ hp
  rw [← he] at this
  exact this

theorem Y_of_a (hG : Formalism.MainNotions.SumRepresentations.At.IdempotentChoiceProperties N r ρ π S) (w : PlE H) (hw : w ∉ placesOver H.E (N.l i))
    (h15 : Nat.card ((Ine (F := H.E) (N.plOm.1 w)).map (N.chi i 1)) = 15)
    (hs : ∀ x, SplitI N r w x)
    (c : Fin R.t) (φ : (S.X' → MatN N i) →ₗ[N.O i] KmodO (N.O i))
    (hφ : ∀ a, InR' N r S a → ∀ y, InY N r S y → φ (a * y) = S.ψχ c a • φ y)
    (γ : GE N) (hγ : γ ∈ Ine (F := H.E) (N.plOm.1 w)) : φ (yg N r S γ) = 0 := by
  obtain ⟨γ', hγ', hu⟩ := exists_unit_of_card N w h15
  obtain ⟨hIn, hψ⟩ := psiChi_span N r hG c (m := 2) ![1, -1]
    (fun k => by
      fin_cases k
      · exact (N.T i).one_mem
      · exact (N.T i).neg_mem (N.T i).one_mem) ![γ', 1]
  refine phi_yg_zero N r c φ hφ γ _ hIn ?_ ?_
  · funext x'
    show (∑ k : Fin 2, (![1, -1] : Fin 2 → N.X i → N.O i) k (S.p x') •
      rO N i r (S.p x') ((![γ', 1] : Fin 2 → GE N) k)) * yg N r S γ x' = 0
    have h1 : (∑ k : Fin 2, (![1, -1] : Fin 2 → N.X i → N.O i) k (S.p x') •
        rO N i r (S.p x') ((![γ', 1] : Fin 2 → GE N) k)) =
        ((r (S.p x') γ' : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)) - 1 := by
      simp [Fin.sum_univ_two, sub_eq_add_neg, rO]
    rw [h1, yg_eq, mul_smul_comm, ← mul_assoc, quad_of_split N r (hs _) γ' γ hγ' hγ, zero_mul, smul_zero]
  · rw [hψ]
    have h2 : ∑ k : Fin 2, (![1, -1] : Fin 2 → N.X i → N.O i) k π *
        ((chiU N i ((c : ℕ) + 1) ((![γ', 1] : Fin 2 → GE N) k) : (N.O i)ˣ) : N.O i) = chi1 N i γ' - 1 := by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.one_apply, Pi.neg_apply,
        one_mul, map_one, Units.val_one, mul_one]
      rw [character_eq_first_off_l N w hw _ (by omega) (by have := c.2; omega) _ hγ', sub_eq_add_neg]
      rfl
    rw [h2]
    exact hu

end G5c

section Cont

theorem norm_le_one_of_root {K : Type} [NormedField K] [IsUltrametricDist K] (y : K) (p : K[X])
    (hp : p.Monic) (hc : ∀ k, ‖p.coeff k‖ ≤ 1) (hy : p.eval y = 0) : ‖y‖ ≤ 1 := by
  by_contra hcon
  push Not at hcon
  rw [eval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_mul] at hy
  rcases Nat.eq_zero_or_pos p.natDegree with h0 | hpos
  · rw [h0] at hy
    simp at hy
  have h1 : y ^ p.natDegree = - ∑ k ∈ Finset.range p.natDegree, p.coeff k * y ^ k := by
    linear_combination hy
  have h2 : ‖∑ k ∈ Finset.range p.natDegree, p.coeff k * y ^ k‖ ≤ ‖y‖ ^ (p.natDegree - 1) := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [norm_mul, norm_pow]
    calc ‖p.coeff k‖ * ‖y‖ ^ k ≤ 1 * ‖y‖ ^ k := by gcongr; exact hc k
      _ = ‖y‖ ^ k := one_mul _
      _ ≤ ‖y‖ ^ (p.natDegree - 1) := pow_le_pow_right₀ hcon.le (by omega)
  have h3 : ‖y‖ ^ p.natDegree ≤ ‖y‖ ^ (p.natDegree - 1) := by
    rw [← norm_pow, h1, norm_neg]
    exact h2
  have h4 : ‖y‖ ^ (p.natDegree - 1) < ‖y‖ ^ p.natDegree := pow_lt_pow_right₀ hcon (by omega)
  exact absurd h3 (not_le.2 h4)

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

theorem norm_iotaOQ_le_one (a : N.O i) : ‖iotaOQ N A i a‖ ≤ 1 := by
  obtain ⟨p, hp, hpa⟩ := Algebra.IsIntegral.isIntegral (R := ℤ_[N.l i]) a
  refine norm_le_one_of_root _ (p.map ((iotaOQ N A i).comp (algebraMap ℤ_[N.l i] (N.O i)))) (hp.map _)
    (fun k => ?_) ?_
  · rw [coeff_map]
    have : ((iotaOQ N A i).comp (algebraMap ℤ_[N.l i] (N.O i))) (p.coeff k) =
        algebraMap ℚ_[N.l i] (Qbar (N.l i)) ((p.coeff k : ℤ_[N.l i]) : ℚ_[N.l i]) := A.iotaQ_alg i _
    rw [this, norm_algebraMap']
    exact PadicInt.norm_le_one _
  · rw [eval_map, ← hom_eval₂, hpa, map_zero]

theorem norm_iotaOQ_unit (u : (N.O i)ˣ) : ‖iotaOQ N A i (u : N.O i)‖ = 1 := by
  refine le_antisymm (norm_iotaOQ_le_one N A i _) ?_
  have h1 : ‖iotaOQ N A i (u : N.O i)‖ * ‖iotaOQ N A i ((u⁻¹ : (N.O i)ˣ) : N.O i)‖ = 1 := by
    rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
  have h2 := norm_iotaOQ_le_one N A i ((u⁻¹ : (N.O i)ˣ) : N.O i)
  nlinarith [norm_nonneg (iotaOQ N A i (u : N.O i))]

theorem norm_iotaOQ_l : ‖iotaOQ N A i ((N.l i : ℕ) : N.O i)‖ < 1 := by
  have : iotaOQ N A i ((N.l i : ℕ) : N.O i) = algebraMap ℚ_[N.l i] (Qbar (N.l i)) ((N.l i : ℕ) : ℚ_[N.l i]) := by
    rw [map_natCast, map_natCast]
  rw [this, norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem norm_iotaOQ_irreducible {ϖ : N.O i} (hϖ : Irreducible ϖ) : ‖iotaOQ N A i ϖ‖ < 1 := by
  have hl := norm_iotaOQ_l N A i
  have hl0 : ((N.l i : ℕ) : N.O i) ≠ 0 := by
    intro h
    have h1 : iotaOQ N A i ((N.l i : ℕ) : N.O i) = ((N.l i : ℕ) : Qbar (N.l i)) := map_natCast _ _
    rw [h, map_zero] at h1
    exact (Nat.cast_ne_zero.2 (N.lPrime i).out.ne_zero) h1.symm
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  rw [hu, map_mul, map_pow, norm_mul, norm_pow, norm_iotaOQ_unit, one_mul] at hl
  by_contra hcon
  push Not at hcon
  exact absurd (one_le_pow₀ hcon) (not_le.2 hl)

theorem continuous_iotaOQ : Continuous (iotaOQ N A i) := by
  apply continuous_of_continuousAt_zero (iotaOQ N A i)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (N.O i)
  have hlt := norm_iotaOQ_irreducible N A i hϖ
  unfold ContinuousAt
  rw [map_zero, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hlt
  have hU : ((IsLocalRing.maximalIdeal (N.O i) ^ n : Ideal _) : Set (N.O i)) ∈ nhds 0 :=
    ((isAdic_iff.mp (N.O_adic i)).1 n).mem_nhds (Ideal.zero_mem _)
  refine Filter.eventually_of_mem hU fun a ha => ?_
  rw [SetLike.mem_coe, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ha
  obtain ⟨b, rfl⟩ := ha
  rw [dist_zero_right, map_mul, map_pow, norm_mul, norm_pow]
  calc ‖iotaOQ N A i b‖ * ‖iotaOQ N A i ϖ‖ ^ n ≤ 1 * ‖iotaOQ N A i ϖ‖ ^ n := by
        gcongr
        exact norm_iotaOQ_le_one N A i b
    _ < ε := by rw [one_mul]; exact hn

theorem contQ_of_continuous {a : ℕ} (ρ : G H.E N.Om →* GL (Fin a) (N.O i))
    (h : Continuous (fun g => ((ρ g : GL (Fin a) (N.O i)) : Matrix (Fin a) (Fin a) (N.O i)))) :
    At.ContQ N i (mapRep (iotaOQ N A i) ρ) :=
  h.matrix_map (continuous_iotaOQ N A i)

end Cont

section G5b

theorem toLinAlgEquiv'_eq {K : Type} [CommRing K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    (Matrix.toLinAlgEquiv' M : Module.End K (Fin n → K)) = Matrix.toLin' M := rfl

theorem kill_descend {O K : Type} [CommRing O] [Field K] (f : O →+* K) (hf : Function.Injective f) {n : ℕ}
    (Mo Go : Matrix (Fin n) (Fin n) O) (p : O[X]) (c : O)
    (h : (aeval (Matrix.toLinAlgEquiv' (Mo.map f) : Module.End K (Fin n → K)) (p.map f)) *
      ((Matrix.toLinAlgEquiv' (Go.map f) : Module.End K (Fin n → K)) -
        algebraMap K (Module.End K (Fin n → K)) (f c)) = 0) :
    aeval Mo p * (Go - c • (1 : Matrix (Fin n) (Fin n) O)) = 0 := by
  have h1 : aeval (Matrix.toLinAlgEquiv' (Mo.map f) : Module.End K (Fin n → K)) (p.map f) =
      Matrix.toLinAlgEquiv' (aeval (Mo.map f) (p.map f)) :=
    Polynomial.aeval_algHom_apply
      (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) K ≃ₐ[K] Module.End K (Fin n → K)).toAlgHom _ _
  rw [h1, ← AlgEquiv.commutes (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) K ≃ₐ[K] Module.End K (Fin n → K))
    (f c), ← map_sub, ← map_mul] at h
  have h2 := (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) K ≃ₐ[K] Module.End K (Fin n → K)).injective
    (h.trans (map_zero _).symm)
  have hcomp : (algebraMap K (Matrix (Fin n) (Fin n) K)).comp f =
      (f.mapMatrix : Matrix (Fin n) (Fin n) O →+* Matrix (Fin n) (Fin n) K).comp
        (algebraMap O (Matrix (Fin n) (Fin n) O)) := by
    ext a j k
    by_cases hjk : j = k <;> simp [Matrix.algebraMap_matrix_apply, hjk]
  apply Matrix.map_injective hf
  show f.mapMatrix _ = f.mapMatrix 0
  rw [map_mul, map_sub, map_zero, Polynomial.map_aeval_eq_aeval_map hcomp]
  have h3 : f.mapMatrix (c • (1 : Matrix (Fin n) (Fin n) O)) = algebraMap K (Matrix (Fin n) (Fin n) K) (f c) := by
    ext j k
    by_cases hjk : j = k <;> simp [Matrix.algebraMap_matrix_apply, hjk]
  rw [h3]
  exact h2

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i)))

theorem weil_deligne_clause_of_split (hG1 : At.G1 N i r) (w : PlE H) {K : Type} [Field K] (f : N.O i →+* K)
    (hf : Function.Injective f)
    (hdec : ∀ x, ∃ U U' : Submodule K (Fin R.nV → K), IsCompl U U' ∧ Module.finrank K U' = R.t ∧
      ∀ γ ∈ Ine (F := H.E) (N.plOm.1 w),
        (∀ v ∈ U, ((mapRep f (r x) γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) K).mulVec v ∈ U) ∧
        (∀ v ∈ U', ((mapRep f (r x) γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) K).mulVec v =
          f (chi1 N i γ) • v))
    (hmult : ∀ x, (((redRep N i (r x) (N.gam0 i w) : GL _ _) :
        Matrix (Fin R.nV) (Fin R.nV) (IsLocalRing.ResidueField (N.O i))).charpoly).rootMultiplicity
      (IsLocalRing.residue (N.O i) (chi1 N i (N.gam0 i w))) = R.t) :
    ∃ Pp : Polynomial (N.T i),
      IsUnit (Pp.eval (algebraMap (N.O i) (N.T i) (chi1 N i (N.gam0 i w)))) ∧
      ∀ x, ∀ γ ∈ Ine (F := H.E) (N.plOm.1 w),
        Polynomial.aeval ((r x (N.gam0 i w) : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i))
            (Pp.map ((Pi.evalRingHom (fun _ : N.X i => N.O i) x).comp (N.T i).val.toRingHom)) *
          (((r x γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)) - chi1 N i γ • 1) = 0 := by
  let _ : Algebra (N.O i) K := f.toAlgebra
  obtain ⟨F, -, hF⟩ := Formalism.IrreducibleCountingLemmas.Z.first_charpoly_in_T (N.O i) (N.X i) (N.T i) R.nV
    (fun x => ((r x (N.gam0 i w) : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)))
    (fun j => by
      obtain ⟨g, hg⟩ := hG1 (N.gam0 i w) j
      have : (fun x => (Matrix.charpolyRev ((r x (N.gam0 i w) : GL (Fin R.nV) (N.O i)) :
          Matrix (Fin R.nV) (Fin R.nV) (N.O i))).coeff j) = (g : N.X i → N.O i) := by
        funext x
        exact (hg x).symm
      rw [this]
      exact g.2)
  choose U U' hc hfr hst using hdec
  have key : ∀ γ ∈ Ine (F := H.E) (N.plOm.1 w), ∃ P : Polynomial (N.T i), P.Monic ∧
      F = P * (X - C (algebraMap (N.O i) (N.T i) (chi1 N i (N.gam0 i w)))) ^ R.t ∧
      IsUnit (P.eval (algebraMap (N.O i) (N.T i) (chi1 N i (N.gam0 i w)))) ∧
      ∀ x, (aeval (Matrix.toLinAlgEquiv' (((r x (N.gam0 i w) : GL _ _) :
          Matrix (Fin R.nV) (Fin R.nV) (N.O i)).map f) : Module.End K (Fin R.nV → K))
          ((P.map (Formalism.IrreducibleCountingLemmas.Z.ev (N.T i) x)).map f)) *
        ((Matrix.toLinAlgEquiv' (((r x γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)).map f) :
          Module.End K (Fin R.nV → K)) - algebraMap K (Module.End K (Fin R.nV → K)) (f (chi1 N i γ))) = 0 := by
    intro γ hγ
    exact Formalism.IrreducibleCountingLemmas.Z.fifth_assembly_second (N.O i) K hf (N.X i) (N.T i) (N.T_local i)
      (fun _ => Fin R.nV → K) U U'
      (fun x => Matrix.toLinAlgEquiv' (((r x (N.gam0 i w) : GL _ _) :
          Matrix (Fin R.nV) (Fin R.nV) (N.O i)).map f))
      (fun x => Matrix.toLinAlgEquiv' (((r x γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)).map f))
      (chi1 N i (N.gam0 i w)) (chi1 N i γ) R.t F
      (fun x => by
        rw [hF x, toLinAlgEquiv'_eq, Matrix.charpoly_toLin', Matrix.charpoly_map]
        rfl)
      hc
      (fun x v hv => ((hst x _ (N.locNd_chebotarevPlace_mem i w)).1 v hv))
      (fun x v hv => ((hst x γ hγ).1 v hv))
      (fun x v hv => ((hst x _ (N.locNd_chebotarevPlace_mem i w)).2 v hv))
      (fun x v hv => ((hst x γ hγ).2 v hv))
      hfr
      (fun x => by
        rw [hF x, ← Matrix.charpoly_map]
        exact hmult x)
  obtain ⟨P0, -, hP0, hu0, -⟩ := key _ (N.locNd_chebotarevPlace_mem i w)
  refine ⟨P0, hu0, fun x γ hγ => ?_⟩
  obtain ⟨P, -, hP, -, hk⟩ := key γ hγ
  have hPP : P = P0 :=
    ((monic_X_sub_C (algebraMap (N.O i) (N.T i) (chi1 N i (N.gam0 i w)))).pow R.t).isRegular.right
      (hP.symm.trans hP0)
  subst hPP
  exact kill_descend f hf _ _ _ _ (hk x)

theorem weil_deligne_clause_of_decomposition (A : NAut N) (hT : At.TieGal N A) (hG1 : At.G1 N i r) (w : PlE H)
    (hw : w ∉ placesOver H.E (N.l i))
    (hcont : ∀ x, At.ContQ N i (mapRep (iotaOQ N A i) (r x)))
    (hwd : ∀ x, ∃ p q : A.LP w, A.wdOf i (mapRep (iotaOQ N A i) (r x)) w = A.lpSum p q ∧ A.lpDim q = R.t ∧
      A.mono0 q ∧ ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w),
        A.inePol q σ = (X - C (iotaO N A i (chi1 N i σ))) ^ R.t)
    (hmult : ∀ x, (((redRep N i (r x) (N.gam0 i w) : GL _ _) :
        Matrix (Fin R.nV) (Fin R.nV) (IsLocalRing.ResidueField (N.O i))).charpoly).rootMultiplicity
      (IsLocalRing.residue (N.O i) (chi1 N i (N.gam0 i w))) = R.t) :
    ∃ Pp : Polynomial (N.T i),
      IsUnit (Pp.eval (algebraMap (N.O i) (N.T i) (chi1 N i (N.gam0 i w)))) ∧
      ∀ x, ∀ γ ∈ Ine (F := H.E) (N.plOm.1 w),
        Polynomial.aeval ((r x (N.gam0 i w) : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i))
            (Pp.map ((Pi.evalRingHom (fun _ : N.X i => N.O i) x).comp (N.T i).val.toRingHom)) *
          (((r x γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)) - chi1 N i γ • 1) = 0 := by
  refine weil_deligne_clause_of_split N r hG1 w (iotaOQ N A i)
    ((A.iotaQ i).injective.comp (IsFractionRing.injective (N.O i) (FractionRing (N.O i)))) (fun x => ?_) hmult
  obtain ⟨p, q, h1, h2, h3, h4⟩ := hwd x
  obtain ⟨U, U', hc, -, hU', hst, hsc⟩ := (hT.2.2.2 i).1 R.nV _ (hcont x) w hw p q h1
  refine ⟨U, U', hc, hU'.trans h2, fun γ hγ => ⟨(hst γ hγ).1, ?_⟩⟩
  refine hsc h3 γ hγ (iotaOQ N A i (chi1 N i γ)) ?_
  rw [h2, h4 γ hγ]
  rfl

theorem rhobar_fac (hC : Cheb N) (hr : GoodR N i r)
    (rb : G H.E N.Om →* GL (Fin R.r) (IsLocalRing.ResidueField (N.O i))) (hrb : IsRhoBar N i rb)
    (x : N.X i) (g : G H.E N.Om) :
    ((rb g : GL _ _) : Matrix (Fin R.r) (Fin R.r) _).charpoly *
      ∏ c ∈ Finset.Icc 1 R.t, (X - C (IsLocalRing.residue (N.O i) ((N.chi i c g : (N.O i)ˣ) : N.O i))) =
    ((redRep N i (r x) g : GL _ _) :
      Matrix (Fin R.nV) (Fin R.nV) (IsLocalRing.ResidueField (N.O i))).charpoly := by
  have hfin : (placesOver H.E (N.l i) ∪ ↑(N.S i) ∪ ↑(N.Q i) : Set (PlE H)).Finite :=
    ((placesOver_finite H.E (N.l i) (N.lPrime i).out.ne_zero).union (N.S i).finite_toSet).union
      (N.Q i).finite_toSet
  have hD := dense_iff_closure_eq.2 (hC _ hfin)
  have hm : IsOpen ((IsLocalRing.maximalIdeal (N.O i) : Ideal (N.O i)) : Set (N.O i)) := by
    have := (isAdic_iff.1 (N.O_adic i)).1 1
    rwa [pow_one] at this
  have o1 : IsOpen {h : G H.E N.Om | g⁻¹ * h ∈ rb.ker} :=
    hrb.1.preimage (continuous_const.mul continuous_id)
  have o2 : IsOpen {h : G H.E N.Om | ∀ a b, ((r x h : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)) a b -
      ((r x g : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)) a b ∈ IsLocalRing.maximalIdeal (N.O i)} := by
    have e : {h : G H.E N.Om | ∀ a b, ((r x h : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)) a b -
        ((r x g : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)) a b ∈ IsLocalRing.maximalIdeal (N.O i)} =
        ⋂ a, ⋂ b, (fun h : G H.E N.Om => ((r x h : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)) a b -
          ((r x g : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)) a b) ⁻¹'
          ((IsLocalRing.maximalIdeal (N.O i) : Ideal (N.O i)) : Set (N.O i)) := by
      ext h
      simp
    rw [e]
    refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => hm.preimage ?_
    exact (((continuous_apply b).comp ((continuous_apply a).comp (hr x).1))).sub continuous_const
  have o3 : IsOpen {h : G H.E N.Om | ∀ c ∈ Finset.Icc 1 R.t, ((N.chi i c h : (N.O i)ˣ) : N.O i) -
      ((N.chi i c g : (N.O i)ˣ) : N.O i) ∈ IsLocalRing.maximalIdeal (N.O i)} := by
    have e : {h : G H.E N.Om | ∀ c ∈ Finset.Icc 1 R.t, ((N.chi i c h : (N.O i)ˣ) : N.O i) -
        ((N.chi i c g : (N.O i)ˣ) : N.O i) ∈ IsLocalRing.maximalIdeal (N.O i)} =
        ⋂ c ∈ Finset.Icc 1 R.t, (fun h : G H.E N.Om => ((N.chi i c h : (N.O i)ˣ) : N.O i) -
          ((N.chi i c g : (N.O i)ˣ) : N.O i)) ⁻¹'
          ((IsLocalRing.maximalIdeal (N.O i) : Ideal (N.O i)) : Set (N.O i)) := by
      ext h
      simp
    rw [e]
    exact isOpen_biInter_finset fun c _ => hm.preimage ((N.chi_cont i c).sub continuous_const)
  obtain ⟨σ, ⟨⟨h1, h2⟩, h3⟩, ⟨w, hw, hsp, B, hB, hF⟩⟩ := hD.inter_open_nonempty _ ((o1.inter o2).inter o3)
    ⟨g, ⟨by simp, by simp⟩, by simp⟩
  simp only [Set.mem_union, not_or, Finset.mem_coe] at hw
  have hres : ∀ a b : N.O i, a - b ∈ IsLocalRing.maximalIdeal (N.O i) →
      IsLocalRing.residue (N.O i) a = IsLocalRing.residue (N.O i) b := fun a b h => Ideal.Quotient.eq.2 h
  have e1 : rb σ = rb g := by
    have : rb (g⁻¹ * σ) = 1 := h1
    rw [map_mul, map_inv, inv_mul_eq_one] at this
    exact this.symm
  have e2 : ((redRep N i (r x) σ : GL _ _) :
      Matrix (Fin R.nV) (Fin R.nV) (IsLocalRing.ResidueField (N.O i))) =
      ((redRep N i (r x) g : GL _ _) :
        Matrix (Fin R.nV) (Fin R.nV) (IsLocalRing.ResidueField (N.O i))) := by
    ext a b
    exact hres _ _ (h2 a b)
  have e3 : ∏ c ∈ Finset.Icc 1 R.t, (X - C (IsLocalRing.residue (N.O i) ((N.chi i c σ : (N.O i)ˣ) : N.O i))) =
      ∏ c ∈ Finset.Icc 1 R.t, (X - C (IsLocalRing.residue (N.O i) ((N.chi i c g : (N.O i)ˣ) : N.O i))) :=
    Finset.prod_congr rfl fun c hc => by rw [hres _ _ (h3 c hc)]
  have hso : SplitOut N i w := ⟨hsp, hw.1.1, hw.1.2, hw.2⟩
  have k1 := hrb.2 x w hso B σ hB hF
  have k2 := (hr x).2.2 w hso B σ hB hF
  rw [← e1, ← e2, ← e3, k1, ← k2, ← Matrix.charpoly_map]
  rfl

theorem mult_of_rhobar (hC : Cheb N) (hr : GoodR N i r)
    (rb : G H.E N.Om →* GL (Fin R.r) (IsLocalRing.ResidueField (N.O i))) (hrb : IsRhoBar N i rb)
    (w : PlE H) (hw : w ∉ placesOver H.E (N.l i))
    (hnr : ¬ (((rb (N.gam0 i w) : GL _ _) : Matrix (Fin R.r) (Fin R.r) _).charpoly).IsRoot
      (IsLocalRing.residue (N.O i) (chi1 N i (N.gam0 i w)))) (x : N.X i) :
    (((redRep N i (r x) (N.gam0 i w) : GL _ _) :
        Matrix (Fin R.nV) (Fin R.nV) (IsLocalRing.ResidueField (N.O i))).charpoly).rootMultiplicity
      (IsLocalRing.residue (N.O i) (chi1 N i (N.gam0 i w))) = R.t := by
  rw [← rhobar_fac N r hC hr rb hrb x (N.gam0 i w)]
  have e : ∏ c ∈ Finset.Icc 1 R.t,
      (X - C (IsLocalRing.residue (N.O i) ((N.chi i c (N.gam0 i w) : (N.O i)ˣ) : N.O i))) =
      (X - C (IsLocalRing.residue (N.O i) (chi1 N i (N.gam0 i w)))) ^ R.t := by
    rw [Finset.prod_congr rfl (g := fun _ => X - C (IsLocalRing.residue (N.O i) (chi1 N i (N.gam0 i w))))
      (fun c hc => by
        rw [Finset.mem_Icc] at hc
        rw [character_eq_first_off_l N w hw c hc.1 hc.2 _ (N.locNd_chebotarevPlace_mem i w)]
        rfl)]
    simp
  rw [e, rootMultiplicity_mul (mul_ne_zero (Matrix.charpoly_monic _).ne_zero
    (pow_ne_zero _ (X_sub_C_ne_zero _))), rootMultiplicity_eq_zero hnr, rootMultiplicity_X_sub_C_pow, zero_add]

theorem rootMult_le_of_maps {O K k : Type} [CommRing O] [Field K] [Field k] (f : O →+* K)
    (hf : Function.Injective f) (g : O →+* k) (F : O[X]) (hF : F.Monic) (c : O) :
    (F.map f).rootMultiplicity (f c) ≤ (F.map g).rootMultiplicity (g c) := by
  have h1 : (X - C (f c)) ^ (F.map f).rootMultiplicity (f c) ∣ F.map f := pow_rootMultiplicity_dvd _ _
  have h2 : ((X - C c) ^ (F.map f).rootMultiplicity (f c)).map f ∣ F.map f := by
    simpa using h1
  have h3 := (Polynomial.map_dvd_map f hf ((monic_X_sub_C c).pow _)).1 h2
  rw [le_rootMultiplicity_iff (hF.map g).ne_zero]
  simpa using Polynomial.map_dvd g h3

def At.LGCat (A : NAut N) (w : PlE H) : Prop :=
  ∀ x, ∃ P, A.ptV i P = some x ∧
    A.wdOf i (mapRep (iotaOQ N A i) (r x)) w = A.lpTw (A.locV i P w) ((1 - (R.nV : ℝ)) / 2)

theorem exists_inertia_charpoly_factor_of_tame_type (A : NAut N) (hC : Cheb N) (hr : GoodR N i r) (hT : At.TieGal N A) (hTY : At.MonodromyInertiaType N A)
    (w : PlE H) (hS : w ∈ N.S i) (hg : ∃ k, w ∈ placesOver H.E (H.g k))
    (hL : At.LGCat N r A w)
    (rb : G H.E N.Om →* GL (Fin R.r) (IsLocalRing.ResidueField (N.O i))) (hrb : IsRhoBar N i rb)
    (hnr : ¬ (((rb (N.gam0 i w) : GL _ _) : Matrix (Fin R.r) (Fin R.r) _).charpoly).IsRoot
      (IsLocalRing.residue (N.O i) (chi1 N i (N.gam0 i w)))) :
    ∃ Pp : Polynomial (N.T i),
      IsUnit (Pp.eval (algebraMap (N.O i) (N.T i) (chi1 N i (N.gam0 i w)))) ∧
      ∀ x, ∀ γ ∈ Ine (F := H.E) (N.plOm.1 w),
        Polynomial.aeval ((r x (N.gam0 i w) : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i))
            (Pp.map ((Pi.evalRingHom (fun _ : N.X i => N.O i) x).comp (N.T i).val.toRingHom)) *
          (((r x γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)) - chi1 N i γ • 1) = 0 := by
  have hw : w ∉ placesOver H.E (N.l i) := N.SQ_l i w (Or.inl hS)
  have hcont : ∀ x, At.ContQ N i (mapRep (iotaOQ N A i) (r x)) :=
    fun x => contQ_of_continuous N A i (r x) (hr x).1
  have hmult := mult_of_rhobar N r hC hr rb hrb w hw hnr
  refine weil_deligne_clause_of_decomposition N r A hT (charpoly_clause_of_chebotarev N hC i r hr) w hw hcont (fun x => ?_) hmult
  obtain ⟨P, -, hP⟩ := hL x
  have hinj : Function.Injective (iotaO N A i) :=
    ((A.iotaQC i).injective.comp (A.iotaQ i).injective).comp
      (IsFractionRing.injective (N.O i) (FractionRing (N.O i)))
  have hine : A.inePol (A.locV i P w) (N.gam0 i w) =
      (((r x (N.gam0 i w) : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)).charpoly).map (iotaO N A i) := by
    rw [← A.inePol_tw (A.locV i P w) ((1 - (R.nV : ℝ)) / 2) _ (N.locNd_chebotarevPlace_mem i w), ← hP,
      ← A.wdOf_ine i _ w hw (hcont x) _ (N.locNd_chebotarevPlace_mem i w)]
    have : ((mapRep (iotaOQ N A i) (r x) (N.gam0 i w) : GL _ _) :
        Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i))) =
        ((r x (N.gam0 i w) : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)).map (iotaOQ N A i) := rfl
    rw [this, Matrix.charpoly_map, Polynomial.map_map]
    rfl
  have hle : (A.inePol (A.locV i P w) (N.gam0 i w)).rootMultiplicity
      (iotaO N A i (chi1 N i (N.gam0 i w))) ≤ R.t := by
    rw [hine]
    refine (rootMult_le_of_maps (iotaO N A i) hinj (IsLocalRing.residue (N.O i)) _
      (Matrix.charpoly_monic _) _).trans (le_of_eq ?_)
    rw [← Matrix.charpoly_map]
    exact hmult x
  obtain ⟨a, b, h1, -, h3, h4, h5⟩ := hTY.2.1 i P w hS hg (N.restN_tameGenerator_generates i w (Or.inl hS)).2 hle
  refine ⟨A.lpTw a ((1 - (R.nV : ℝ)) / 2), A.lpTw b ((1 - (R.nV : ℝ)) / 2), ?_, ?_, ?_, ?_⟩
  · rw [hP, h1, A.lpTw_sum]
  · rw [A.lpDim_tw, h3]
  · exact (A.monomial_twist_iff _ _).2 h4
  · intro σ hσ
    rw [A.inePol_tw _ _ σ hσ, h5 σ hσ]

end G5b

section Maschke

variable {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ}

theorem isSSRep_of_finite [CharZero k] (ρ : Γ →* GL (Fin a) k) (hfin : (Set.range ρ).Finite) :
    IsSSRep ρ := by
  intro W hW
  have hF : Finite ρ.range := by
    have h1 : ((ρ.range : Subgroup (GL (Fin a) k)) : Set (GL (Fin a) k)) = Set.range ρ := MonoidHom.coe_range ρ
    have h2 : ((ρ.range : Subgroup (GL (Fin a) k)) : Set (GL (Fin a) k)).Finite := h1 ▸ hfin
    exact h2.to_subtype
  have hN : NeZero ((Nat.card ρ.range : ℕ) : k) := ⟨Nat.cast_ne_zero.2 Nat.card_pos.ne'⟩
  have hss : Representation.IsSemisimpleRepresentation (glRep ρ.range.subtype) := inferInstance
  obtain ⟨W', hW'⟩ := hss.exists_isCompl ⟨W, by
    rintro ⟨_, γ, rfl⟩ v hv
    exact hW γ v hv⟩
  refine ⟨W'.toSubmodule, fun γ v hv => W'.apply_mem_toSubmodule ⟨ρ γ, γ, rfl⟩ hv, ?_, ?_⟩
  · rw [disjoint_iff]
    exact congrArg Subrepresentation.toSubmodule hW'.inf_eq_bot
  · rw [codisjoint_iff]
    exact congrArg Subrepresentation.toSubmodule hW'.sup_eq_top

def diagHom (k : Type) [Field k] (r n : ℕ) : kˣ →* GL (Fin n) k :=
  (Units.map (Matrix.diagonalRingHom (Fin n) k).toMonoidHom).comp
    ((MulEquiv.piUnits (M := fun _ : Fin n => k)).symm.toMonoidHom.comp
      (MonoidHom.pi fun j : Fin n => if (j : ℕ) < r then (1 : kˣ →* kˣ) else MonoidHom.id kˣ))

theorem diagHom_coe (r n : ℕ) (u : kˣ) :
    ((diagHom k r n u : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      Matrix.diagonal (fun j : Fin n => if (j : ℕ) < r then 1 else (u : k)) := by
  show Matrix.diagonal _ = _
  congr 1
  funext j
  show (((if (j : ℕ) < r then (1 : kˣ →* kˣ) else MonoidHom.id kˣ) u : kˣ) : k) = _
  split_ifs <;> rfl

theorem diagHom_charpoly (r t : ℕ) (u : kˣ) :
    ((diagHom k r (r + t) u : GL (Fin (r + t)) k) : Matrix (Fin (r + t)) (Fin (r + t)) k).charpoly =
      (X - 1) ^ r * (X - C (u : k)) ^ t := by
  rw [diagHom_coe, Matrix.charpoly_diagonal, Fin.prod_univ_add]
  simp

theorem split_of_charpoly [CharZero k] {r t : ℕ} (ht : t ≠ 0) (ρ : Γ →* GL (Fin (r + t)) k) (χ : Γ →* kˣ)
    (hfin : (Set.range ρ).Finite)
    (hch : ∀ γ, ((ρ γ : GL _ _) : Matrix (Fin (r + t)) (Fin (r + t)) k).charpoly =
      (X - 1) ^ r * (X - C (χ γ : k)) ^ t) :
    ∃ Pm : GL (Fin (r + t)) k, ∀ γ, ((Pm⁻¹ * ρ γ * Pm : GL _ _) : Matrix (Fin (r + t)) (Fin (r + t)) k) =
      Matrix.diagonal (fun j : Fin (r + t) => if (j : ℕ) < r then 1 else (χ γ : k)) := by
  have hX : (X - 1 : k[X]) ≠ 0 := by simpa using X_sub_C_ne_zero (1 : k)
  have hdet : ∀ γ γ', ρ γ' = ρ γ → χ γ' = χ γ := by
    intro γ γ' h
    have h1 := hch γ'
    rw [h, hch γ] at h1
    have h2 := mul_left_cancel₀ (pow_ne_zero r hX) h1
    have h3 := congrArg (eval (χ γ : k)) h2
    simp only [eval_pow, eval_sub, eval_X, eval_C, sub_self, zero_pow ht] at h3
    have h4 := pow_eq_zero_iff ht |>.1 h3.symm
    exact Units.ext (sub_eq_zero.1 h4).symm
  have hfin2 : (Set.range ((diagHom k r (r + t)).comp χ)).Finite := by
    refine (hfin.image (fun M => diagHom k r (r + t) (χ (Function.invFun ρ M)))).subset ?_
    rintro _ ⟨γ, rfl⟩
    refine ⟨ρ γ, ⟨γ, rfl⟩, ?_⟩
    show diagHom k r (r + t) (χ (Function.invFun ρ (ρ γ))) = diagHom k r (r + t) (χ γ)
    rw [hdet γ _ (Function.invFun_eq ⟨γ, rfl⟩)]
  obtain ⟨Pm, hP⟩ := brauerNesbitt_matrix ρ ((diagHom k r (r + t)).comp χ) (isSSRep_of_finite ρ hfin)
    (isSSRep_of_finite _ hfin2) (fun γ => by
      rw [hch γ]
      exact (diagHom_charpoly r t (χ γ)).symm)
  exact ⟨Pm, fun γ => by
    rw [← hP γ]
    exact diagHom_coe r (r + t) (χ γ)⟩

end Maschke

section G5a

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}
  (r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i)))

theorem SplitI_of_TY (A : NAut N) (hr : GoodR N i r) (w : PlE H) (hw : w ∉ placesOver H.E (N.l i))
    (hL : At.LGCat N r A w)
    (hty : ∀ P : A.AV i, A.mono0 (A.locV i P w) ∧ ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w),
      A.inePol (A.locV i P w) σ = (X - 1) ^ R.r * (X - C (iotaO N A i (chi1 N i σ))) ^ R.t)
    (x : N.X i) : SplitI N r w x := by
  obtain ⟨P, -, hP⟩ := hL x
  have hcont := contQ_of_continuous N A i (r x) (hr x).1
  have hCZ : CharZero (Kf N i) := (A.iotaQ i).charZero
  have hm : A.mono0 (A.wdOf i (mapRep (iotaOQ N A i) (r x)) w) := by
    rw [hP]
    exact (A.monomial_twist_iff _ _).2 (hty P).1
  have hfinQ := (A.wdOf_mono0 i _ w hw hcont).1 hm
  have hΦ : Function.Injective (Units.map ((A.iotaQ i).mapMatrix :
      Matrix (Fin R.nV) (Fin R.nV) (Kf N i) →+* Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i))).toMonoidHom) :=
    Units.map_injective (Matrix.map_injective (A.iotaQ i).injective)
  have hfin : (Set.range ((mapRep (algebraMap (N.O i) (Kf N i)) (r x)).comp
      (Ine (F := H.E) (N.plOm.1 w)).subtype)).Finite := by
    refine Set.Finite.of_finite_image (hfinQ.subset ?_) hΦ.injOn
    rintro _ ⟨_, ⟨γ, rfl⟩, rfl⟩
    exact ⟨γ.1, γ.2, rfl⟩
  have hj : Function.Injective ((A.iotaQC i).toRingHom.comp (A.iotaQ i)) :=
    (A.iotaQC i).injective.comp (A.iotaQ i).injective
  obtain ⟨Pm, hPm⟩ := split_of_charpoly (r := R.r) (t := R.t) R.t_odd.pos.ne'
    ((mapRep (algebraMap (N.O i) (Kf N i)) (r x)).comp (Ine (F := H.E) (N.plOm.1 w)).subtype)
    (((Units.map (algebraMap (N.O i) (Kf N i)).toMonoidHom).comp (N.chi i 1)).comp
      (Ine (F := H.E) (N.plOm.1 w)).subtype) hfin (fun γ => by
      have h1 := A.wdOf_ine i _ w hw hcont γ.1 γ.2
      rw [hP, A.inePol_tw _ _ _ γ.2, (hty P).2 _ γ.2] at h1
      have h2 : ((mapRep (iotaOQ N A i) (r x) γ.1 : GL _ _) :
          Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i))) =
          ((r x γ.1 : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)).map (iotaOQ N A i) := rfl
      rw [h2, Matrix.charpoly_map, Polynomial.map_map] at h1
      apply Polynomial.map_injective _ hj
      have h3 : ((((mapRep (algebraMap (N.O i) (Kf N i)) (r x)).comp
          (Ine (F := H.E) (N.plOm.1 w)).subtype) γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (Kf N i)) =
          ((r x γ.1 : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)).map (algebraMap (N.O i) (Kf N i)) := rfl
      have h4 : (((((mapRep (algebraMap (N.O i) (Kf N i)) (r x)).comp
          (Ine (F := H.E) (N.plOm.1 w)).subtype) γ : GL _ _) :
          Matrix (Fin R.nV) (Fin R.nV) (Kf N i)).charpoly).map ((A.iotaQC i).toRingHom.comp (A.iotaQ i)) =
          (X - 1) ^ R.r * (X - C (iotaO N A i (chi1 N i γ.1))) ^ R.t := by
        rw [h3, Matrix.charpoly_map, Polynomial.map_map]
        exact h1
      refine h4.trans ?_
      simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
        Polynomial.map_one, Polynomial.map_C]
      rfl)
  exact ⟨Pm, fun γ hγ => hPm ⟨γ, hγ⟩⟩

theorem split_inertia_of_hypotheses (A : NAut N) (hr : GoodR N i r) (hTY : At.MonodromyInertiaType N A) (w : PlE H)
    (hSQ : w ∈ N.S i ∨ w ∈ N.Q i)
    (hcond : w ∈ N.Q i ∨ (At.Del N i ∧
      (w ∈ placesOver H.E H.pde ∨ (N.l i = H.pde ∧ w ∈ placesOver H.E H.pde'))))
    (hL : At.LGCat N r A w) (x : N.X i) : SplitI N r w x :=
  SplitI_of_TY N r A hr w (N.SQ_l i w hSQ) hL (fun P => hTY.1 i P w hSQ hcond) x

end G5a

section H0

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) {i : N.Loc}

theorem twisted_character_at_frobenius (w : PlE H) (hw : w ∉ placesOver H.E (N.l i)) (e : ℤ) :
    ((At.chiEpsBar N i e (N.gam0 i w) : (IsLocalRing.ResidueField (N.O i))ˣ) :
      IsLocalRing.ResidueField (N.O i)) = (IsLocalRing.residue (N.O i) (chi1 N i (N.gam0 i w)))⁻¹ := by
  have h1 : Formalism.MainNotions.N.Glob.epsO N i (N.gam0 i w) = 1 := by
    simp [Formalism.MainNotions.N.Glob.epsO, cycZ_one_of_Ine N w hw _ (N.locNd_chebotarevPlace_mem i w)]
  have h2 : (((Units.map (IsLocalRing.residue (N.O i)).toMonoidHom).comp (Formalism.MainNotions.N.Glob.epsO N i)) ^ e)
      (N.gam0 i w) = 1 := by
    have h3 : (((Units.map (IsLocalRing.residue (N.O i)).toMonoidHom).comp (Formalism.MainNotions.N.Glob.epsO N i)) ^ e)
      (N.gam0 i w) = (((Units.map (IsLocalRing.residue (N.O i)).toMonoidHom).comp (Formalism.MainNotions.N.Glob.epsO N i))
      (N.gam0 i w)) ^ e := rfl
    rw [h3, MonoidHom.comp_apply, h1, map_one, one_zpow]
  rw [At.chiEpsBar, MonoidHom.mul_apply, h2, mul_one, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  rfl

theorem invariants_bot_of_not_root (rb : G H.E N.Om →* GL (Fin R.r) (IsLocalRing.ResidueField (N.O i))) (w : PlE H)
    (hw : w ∉ placesOver H.E (N.l i))
    (hnr : ¬ (((rb (N.gam0 i w) : GL _ _) : Matrix (Fin R.r) (Fin R.r) _).charpoly).IsRoot
      (IsLocalRing.residue (N.O i) (chi1 N i (N.gam0 i w)))) (e : ℤ) :
    H0 ((Formalism.MainNotions.N.twistRep (Formalism.MainNotions.N.glRep rb) (At.chiEpsBar N i e)).comp
      (Dec (F := H.E) (N.plOm.1 w)).subtype) = ⊥ := by
  have hc0 : IsLocalRing.residue (N.O i) (chi1 N i (N.gam0 i w)) ≠ 0 :=
    ((Units.isUnit (N.chi i 1 (N.gam0 i w))).map (IsLocalRing.residue (N.O i))).ne_zero
  have hne : ¬ Module.End.HasEigenvalue (Matrix.toLin' ((rb (N.gam0 i w) : GL _ _) :
      Matrix (Fin R.r) (Fin R.r) (IsLocalRing.ResidueField (N.O i))) :
        Module.End (IsLocalRing.ResidueField (N.O i)) (Fin R.r → IsLocalRing.ResidueField (N.O i)))
      (IsLocalRing.residue (N.O i) (chi1 N i (N.gam0 i w))) := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']
    exact hnr
  have hb := Formalism.IrreducibleCountingLemmas.Z.twist_invertible_holds _ _ _ _ hc0 hne
  rw [eq_bot_iff]
  intro v hv
  have h := hv ⟨N.gam0 i w, Ine_le_Dec _ (N.locNd_chebotarevPlace_mem i w)⟩
  have h2 : ((At.chiEpsBar N i e (N.gam0 i w) : (IsLocalRing.ResidueField (N.O i))ˣ) :
      IsLocalRing.ResidueField (N.O i)) • Matrix.toLin' ((rb (N.gam0 i w) : GL _ _) :
      Matrix (Fin R.r) (Fin R.r) (IsLocalRing.ResidueField (N.O i))) v = v := h
  rw [twisted_character_at_frobenius N w hw e] at h2
  rw [Submodule.mem_bot]
  apply hb.1
  show _ - v = _ - 0
  rw [h2, map_zero, smul_zero, sub_self, sub_self]

def At.HOneTwoZero (i : N.Loc) (w : PlE H)
    (ρ : Representation (IsLocalRing.ResidueField (N.O i)) (G H.E N.Om)
      (Fin R.r → IsLocalRing.ResidueField (N.O i))) : Prop :=
  letI : TopologicalSpace (IsLocalRing.ResidueField (N.O i)) := ⊥
  haveI : DiscreteTopology (IsLocalRing.ResidueField (N.O i)) := ⟨rfl⟩
  Subsingleton (H1 (ρ.comp (Dec (F := H.E) (N.plOm.1 w)).subtype)) ∧
  Subsingleton (H2 (ρ.comp (Dec (F := H.E) (N.plOm.1 w)).subtype))

theorem HStarZero_iff (rb : G H.E N.Om →* GL (Fin R.r) (IsLocalRing.ResidueField (N.O i))) (w : PlE H)
    (hw : w ∉ placesOver H.E (N.l i))
    (hnr : ¬ (((rb (N.gam0 i w) : GL _ _) : Matrix (Fin R.r) (Fin R.r) _).charpoly).IsRoot
      (IsLocalRing.residue (N.O i) (chi1 N i (N.gam0 i w)))) (e : ℤ) :
    At.HStarZero N i w (Formalism.MainNotions.N.twistRep (Formalism.MainNotions.N.glRep rb) (At.chiEpsBar N i e)) ↔
      At.HOneTwoZero N i w (Formalism.MainNotions.N.twistRep (Formalism.MainNotions.N.glRep rb) (At.chiEpsBar N i e)) :=
  ⟨fun h => h.2, fun h => ⟨invariants_bot_of_not_root N rb w hw hnr e, h⟩⟩

end H0

section Lin

theorem inj_of_scalars {ι : Type} [DecidableEq ι] {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (θ : V →ₗ[ℂ] W) (θ' : W →ₗ[ℂ] V) (M : ι → Submodule ℂ V)
    (hind : iSupIndep M) (htop : iSup M = ⊤)
    (hl : ∀ σ, ∃ lam : ℂ, lam ≠ 0 ∧ ∀ f ∈ M σ, θ' (θ f) = lam • f) : Function.Injective θ := by
  classical
  choose lam hl0 hl using hl
  rw [injective_iff_map_eq_zero]
  intro f h0
  have hf : f ∈ iSup M := htop ▸ Submodule.mem_top
  obtain ⟨x, rfl⟩ := (Submodule.mem_iSup_iff_exists_dfinsupp M f).1 hf
  have hcomm : (θ' ∘ₗ θ) ∘ₗ (DFinsupp.lsum ℕ fun σ => (M σ).subtype) =
      (DFinsupp.lsum ℕ fun σ => (M σ).subtype) ∘ₗ
        DFinsupp.mapRange.linearMap (fun σ => lam σ • (LinearMap.id : M σ →ₗ[ℂ] M σ)) := by
    refine DFinsupp.lhom_ext fun σ y => ?_
    simp [hl σ y y.2]
  have h1 := LinearMap.congr_fun hcomm x
  simp only [LinearMap.comp_apply, h0, map_zero] at h1
  have h2 : DFinsupp.mapRange.linearMap (fun σ => lam σ • (LinearMap.id : M σ →ₗ[ℂ] M σ)) x = 0 :=
    hind.dfinsupp_lsum_injective (by rw [← h1, map_zero])
  have h3 : x = 0 := by
    ext σ
    have := DFunLike.congr_fun h2 σ
    simp only [DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_apply, LinearMap.smul_apply,
      LinearMap.id_apply, DFinsupp.zero_apply] at this
    rw [(smul_eq_zero.1 this).resolve_left (hl0 σ)]
    rfl
  rw [h3, map_zero]

theorem finrank_biSup {ι : Type} [DecidableEq ι] {W : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (T : ι → Submodule ℂ W) (hind : iSupIndep T) (s : Finset ι) :
    Module.finrank ℂ ↥(⨆ P ∈ s, T P) = ∑ P ∈ s, Module.finrank ℂ (T P) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.iSup_insert, Finset.sum_insert ha, ← ih]
    have hd : Disjoint (T a) (⨆ P ∈ s, T P) :=
      hind.disjoint_biSup (y := (s : Set ι)) (by simpa using ha)
    have := Submodule.finrank_sup_add_finrank_inf_eq (T a) (⨆ P ∈ s, T P)
    rw [hd.eq_bot, finrank_bot, add_zero] at this
    exact this

end Lin

section Z

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem thetaT_injective (i : N.Loc) (hInt : Rows.IsotInternal what₂) (h42 : At.Conclusion42 N A i) :
    Function.Injective (what₂.thetaT (N.mu i) (N.j i)) := by
  have hI := hInt (N.j i) (N.j_range i).1 (N.j_range i).2
  refine inj_of_scalars _ (what₂.thetaP (N.mu i) (N.j i)) (what₂.isot (N.j i)) hI.submodule_iSupIndep
    hI.submodule_iSup_eq_top fun σ => ?_
  by_cases h : what₂.isot (N.j i) σ = ⊥
  · exact ⟨1, one_ne_zero, fun f hf => by rw [h, Submodule.mem_bot] at hf; simp [hf]⟩
  · obtain ⟨lam, h0, hl⟩ := (h42 σ h).1.1; exact ⟨(lam : ℂ), by exact_mod_cast h0.ne', hl⟩

open Classical in

theorem multiplicity_sum_eq_dimension (i : N.Loc) (hInt : Rows.IsotInternal what₂) (h42 : At.Conclusion42 N A i)
    (h2 : (goodPartM N A i).map (what₂.thetaT (N.mu i) (N.j i)) = ⨆ x ∈ ZgoodN N A i, eigC N A i x) :
    ∑ x : N.X i, (if x ∈ ZgoodN N A i then N.mult i x else 0) = dM N A i := by
  have : Fintype (A.AV i) := Fintype.ofFinite _
  have hinj := thetaT_injective N A i hInt h42
  have hd : dM N A i = Module.finrank ℂ ↥((goodPartM N A i).map (what₂.thetaT (N.mu i) (N.j i))) :=
    LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj (goodPartM N A i))
  rw [hd, h2]
  let Fx : N.X i → Finset (A.AV i) := fun x => Finset.univ.filter (fun P => A.ptV i P = some x)
  let Zf : Finset (N.X i) := Finset.univ.filter (· ∈ ZgoodN N A i)
  have he : ∀ x, eigC N A i x = ⨆ P ∈ Fx x, A.typeV i P := by
    intro x
    simp [eigC, Fx]
  have hs : (⨆ x ∈ ZgoodN N A i, eigC N A i x) = ⨆ P ∈ Zf.biUnion Fx, A.typeV i P := by
    rw [Finset.iSup_biUnion]
    simp [Zf, he]
  have hdisj : Set.PairwiseDisjoint (Zf : Set (N.X i)) Fx := by
    intro x _ y _ hxy
    rw [Function.onFun, Finset.disjoint_left]
    intro P hP hP'
    simp only [Fx, Finset.mem_filter, Finset.mem_univ, true_and] at hP hP'
    exact hxy (Option.some.inj (hP.symm.trans hP'))
  rw [hs, finrank_biSup _ (A.typeV_indep i), Finset.sum_biUnion hdisj, ← Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← finrank_biSup _ (A.typeV_indep i), ← he, A.eig_dim]
  rfl

theorem good_part_image_iff (i : N.Loc) (hInt : Rows.IsotInternal what₂) (h42 : At.Conclusion42 N A i)
    (h1 : ∀ x ∈ ZgoodN N A i, ∀ Sig, HasParamX N A i x Sig →
      (MjSig N A i Sig).map (what₂.thetaT (N.mu i) (N.j i)) = eigC N A i x) :
    (goodPartM N A i).map (what₂.thetaT (N.mu i) (N.j i)) = ⨆ x ∈ ZgoodN N A i, eigC N A i x ↔
      goodPartM N A i = ⨆ x ∈ ZgoodN N A i, ⨆ Sig ∈ {Sig | HasParamX N A i x Sig}, MjSig N A i Sig := by
  have hs : (⨆ x ∈ ZgoodN N A i, eigC N A i x) =
      (⨆ x ∈ ZgoodN N A i, ⨆ Sig ∈ {Sig | HasParamX N A i x Sig}, MjSig N A i Sig).map
        (what₂.thetaT (N.mu i) (N.j i)) := by
    simp only [Submodule.map_iSup]
    refine iSup_congr fun x => iSup_congr fun hx => ?_
    obtain ⟨Sig0, hS0, -⟩ := hx.2
    refine le_antisymm ?_ (iSup_le fun Sig => iSup_le fun hS => (h1 x hx Sig hS).le)
    exact le_iSup_of_le Sig0 (le_iSup_of_le hS0 (h1 x hx Sig0 hS0).ge)
  rw [hs]
  exact (Submodule.map_injective_of_injective (thetaT_injective N A i hInt h42)).eq_iff

namespace At

def ReducedMultiplicityStatement (i : N.Loc) : Prop :=
  HG N A i →
    (∀ x ∈ ZgoodN N A i, ∀ Sig, HasParamX N A i x Sig →
      (MjSig N A i Sig).map (what₂.thetaT (N.mu i) (N.j i)) = eigC N A i x) ∧
    (goodPartM N A i).map (what₂.thetaT (N.mu i) (N.j i)) = ⨆ x ∈ ZgoodN N A i, eigC N A i x

end At

theorem multiplicity_statement_iff (i : N.Loc) (hInt : Rows.IsotInternal what₂) (h42 : At.Conclusion42 N A i) :
    At.ConclusionZ N A i ↔ At.ReducedMultiplicityStatement N A i :=
  ⟨fun h hg => ⟨fun x hx Sig hS => ((h hg).1 x hx Sig hS).2, (h hg).2.1⟩,
    fun h hg => ⟨fun x hx Sig hS => ⟨LinearMap.ker_eq_bot.2
        ((thetaT_injective N A i hInt h42).comp Subtype.val_injective), (h hg).1 x hx Sig hS⟩,
      (h hg).2, multiplicity_sum_eq_dimension N A i hInt h42 (h hg).2⟩⟩

end Z

def ReducedMultiplicityStatement (D : D7) : Prop := ∀ i, At.ReducedMultiplicityStatement D.nd D.naut i

theorem multiplicity_statement_iff_reduced (D : D7) (hInt : Rows.IsotInternal D.what₂) (h42 : Conclusion42 D) : ConclusionZ D ↔ ReducedMultiplicityStatement D :=
  forall_congr' fun i => multiplicity_statement_iff D.nd D.naut i hInt (h42 i)

namespace At

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def ReducedAutomorphicNoBrauerNesbitt : Prop :=
  (∀ Pa Pa' : List (Part A.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ p.d = 1) → (∀ p ∈ Pa', 1 ≤ p.a ∧ p.d = 1) →
    (∀ᶠ w in Filter.cofinite, isoLoc N A Pa w = isoLoc N A Pa' w) → Pa.Perm Pa') ∧
  (∀ Pa Pa' : List (Part A.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) →
    (∀ p ∈ Pa', 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) →
    (∀ᶠ w in Filter.cofinite, isoLoc N A Pa w = isoLoc N A Pa' w) → Pa.Perm Pa') ∧
  Cheb N

theorem automorphic_hypotheses_iff_reduced : JacquetShalikaStrongMultOne N A ↔ ReducedAutomorphicNoBrauerNesbitt N A :=
  ⟨fun h => ⟨h.1, h.2.1, h.2.2.1⟩,
    fun h => ⟨h.1, h.2.1, h.2.2, fun _ _ _ ρ ρ' hs hs' hc => brauerNesbitt_matrix ρ ρ' hs hs' hc⟩⟩

def G3a (i : N.Loc) (r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i))) : Prop :=
  ∃ (K' : Type) (_ : Field K') (_ : Algebra (Kf N i) K') (_ : FiniteDimensional (Kf N i) K'),
    ∀ x, (∀ W, IsIrrSub (mapRep ((algebraMap (Kf N i) K').comp (algebraMap (N.O i) (Kf N i))) (r x)) W →
        AbsIrrSub (mapRep ((algebraMap (Kf N i) K').comp (algebraMap (N.O i) (Kf N i))) (r x)) W) ∧
      ∀ W₁ W₂, IsIrrSub (mapRep ((algebraMap (Kf N i) K').comp (algebraMap (N.O i) (Kf N i))) (r x)) W₁ →
        IsIrrSub (mapRep ((algebraMap (Kf N i) K').comp (algebraMap (N.O i) (Kf N i))) (r x)) W₂ →
        W₁ ⊓ W₂ = ⊥ →
        ¬ IsoSub (mapRep ((algebraMap (Kf N i) K').comp (algebraMap (N.O i) (Kf N i))) (r x)) W₁ W₂

def ReducedFamilyProposition (i : N.Loc) : Prop :=
  (∃ rq : N.X i → (G H.E N.Om →* GL (Fin R.nV) (Qbar (N.l i))), ∀ x, IsHeckeGaloisQ N A i x (rq x)) ∧
  (∀ P P' : A.AV i, A.ptV i P ≠ none → A.ptV i P = A.ptV i P' →
    (∀ Pa Pa', IsBCV N A i P Pa → IsBCV N A i P' Pa' → Pa.Perm Pa') ∧
    ∀ w, w ∉ N.S i → w ∉ N.Q i →
      (IsSplitPl H w → A.locV i P w = A.locV i P' w) ∧
      (¬ IsSplitPl H w → ubc R.nV (A.satV i P w) = ubc R.nV (A.satV i P' w))) ∧
  ∀ r, GoodR N i r → G2 N A i r ∧ G3a N i r ∧ G4 N i r

theorem proposition_families_iff (hC : Cheb N) (hO : OLarge N A) (i : N.Loc) : Conclusion41 N A i ↔ ReducedFamilyProposition N A i :=
  ⟨fun h => ⟨h.1.1, h.2.1, fun r hr => ⟨(h.2.2 r hr).2.1, (h.2.2 r hr).2.2.1.1, (h.2.2 r hr).2.2.2⟩⟩,
    fun h => ⟨⟨h.1, exists_GoodR N A hO i h.1⟩, h.2.1, fun r hr => ⟨charpoly_clause_of_chebotarev N hC i r hr, (h.2.2 r hr).1,
      ⟨(h.2.2 r hr).2.1, residual_charpoly_of_chebotarev_clause N i r (charpoly_clause_of_chebotarev N hC i r hr)⟩, (h.2.2 r hr).2.2⟩⟩⟩

def ReducedGaloisClause (i : N.Loc) : Prop :=
  HG N A i → ∀ r, GoodR N i r → ∀ w : PlE H, (w ∈ N.S i ∨ w ∈ N.Q i) →
    w ∉ placesOver H.E (N.l i) →
    ((w ∈ N.Q i ∨ w ∈ placesOver H.E H.pde ∨ (N.l i = H.pde ∧ w ∈ placesOver H.E H.pde')) → ∀ x,
      SplitI N r w x) ∧
    ((∃ k, w ∈ placesOver H.E (H.g k)) → w ∈ N.S i →
      ∃ Pp : Polynomial (N.T i),
        IsUnit (Pp.eval (algebraMap (N.O i) (N.T i) (chi1 N i (N.gam0 i w)))) ∧
        ∀ x, ∀ γ ∈ Ine (F := H.E) (N.plOm.1 w),
          Polynomial.aeval ((r x (N.gam0 i w) : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i))
              (Pp.map ((Pi.evalRingHom (fun _ : N.X i => N.O i) x).comp (N.T i).val.toRingHom)) *
            (((r x γ : GL _ _) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)) - chi1 N i γ • 1) = 0) ∧
    (w ∈ N.S i →
      ∀ rb, IsRhoBar N i rb → ∀ e : ℤ, HStarZero N i w (Formalism.MainNotions.N.twistRep (Formalism.MainNotions.N.glRep rb) (chiEpsBar N i e)))

theorem galois_clause_iff_reduced (i : N.Loc) (hDel : Del N i) : ConclusionG5 N A i ↔ ReducedGaloisClause N A i := by
  constructor
  · intro h hg r hr w hw hl
    obtain ⟨ha, hb, hc⟩ := h hg r hr w hw hl
    exact ⟨fun hq x => (ha hq x).2, hb, fun hS => (hc hS).2⟩
  · intro h hg r hr w hw hl
    obtain ⟨ha, hb, hc⟩ := h hg r hr w hw hl
    refine ⟨fun hq x => ⟨fun γ hγ => quad_of_split N r (ha hq x) γ γ hγ hγ, ha hq x⟩, hb,
      fun hS => ⟨?_, hc hS⟩⟩
    intro ρ π S hG c φ hφ γ hγ
    rcases ((N.S_def i w).1 hS).1 with h0 | h1 | hp
    · obtain ⟨Pp, hu, hk⟩ := hb ⟨0, h0⟩ hS
      exact Y_of_b N r hG w hl Pp hu hk c φ hφ γ hγ
    · obtain ⟨Pp, hu, hk⟩ := hb ⟨1, h1⟩ hS
      exact Y_of_b N r hG w hl Pp hu hk c φ hφ γ hγ
    · refine Y_of_a N r hG w hl (hDel w hS hp) (ha ?_) c φ hφ γ hγ
      by_cases hlp : N.l i = H.pde
      · rw [if_pos hlp] at hp
        exact Or.inr (Or.inr ⟨hlp, hp⟩)
      · rw [if_neg hlp] at hp
        exact Or.inr (Or.inl hp)

def SufficientGaloisClause (i : N.Loc) : Prop :=
  HG N A i → ∀ r, GoodR N i r → ∀ w : PlE H, (w ∈ N.S i ∨ w ∈ N.Q i) →
    LGCat N r A w ∧
    (w ∈ N.S i → (∃ rb, IsRhoBar N i rb) ∧ ∀ rb, IsRhoBar N i rb →
      ¬ (((rb (N.gam0 i w) : GL _ _) : Matrix (Fin R.r) (Fin R.r) _).charpoly).IsRoot
        (IsLocalRing.residue (N.O i) (chi1 N i (N.gam0 i w))) ∧
      ∀ e : ℤ, HOneTwoZero N i w (Formalism.MainNotions.N.twistRep (Formalism.MainNotions.N.glRep rb) (chiEpsBar N i e)))

theorem galois_clause_of_sufficient (hC : Cheb N) (hT : TieGal N A) (hTY : MonodromyInertiaType N A) (i : N.Loc) (hDel : Del N i)
    (h : SufficientGaloisClause N A i) : ConclusionG5 N A i := by
  rw [galois_clause_iff_reduced N A i hDel]
  intro hg r hr w hw hl
  obtain ⟨hL, hS⟩ := h hg r hr w hw
  refine ⟨fun hq x => split_inertia_of_hypotheses N r A hr hTY w hw ?_ hL x, fun hgk hS' => ?_,
    fun hS' rb hrb e => ?_⟩
  · rcases hq with hq | hq
    · exact Or.inl hq
    · exact Or.inr ⟨hDel, hq⟩
  · obtain ⟨⟨rb, hrb⟩, hall⟩ := hS hS'
    exact exists_inertia_charpoly_factor_of_tame_type N r A hC hr hT hTY w hS' hgk hL rb hrb (hall rb hrb).1
  · exact (HStarZero_iff N rb w hl ((hS hS').2 rb hrb).1 e).2 (((hS hS').2 rb hrb).2 e)

end At

def ReducedAutomorphicHypotheses (D : D7) : Prop := At.ReducedAutomorphicNoBrauerNesbitt D.nd D.naut

theorem condition_iff_additive_maps (D : D7) : adm5 D ↔ ReducedAutomorphicHypotheses D := At.automorphic_hypotheses_iff_reduced D.nd D.naut

def tieLab (D : D7) : Prop := At.TieLab D.nd D.naut

def ReducedFamilyProposition (D : D7) : Prop := ∀ i, At.ReducedFamilyProposition D.nd D.naut i
def ReducedParameterProposition (D : D7) : Prop := ∀ i, At.ReducedParameterProposition D.nd D.naut i
def ReducedGaloisClause (D : D7) : Prop := ∀ i, At.ReducedGaloisClause D.nd D.naut i
def SufficientGaloisClause (D : D7) : Prop := ∀ i, At.SufficientGaloisClause D.nd D.naut i

theorem proposition_families_iff (D : D7) (h5 : adm5 D) (hO : hypO D) : Conclusion41 D ↔ ReducedFamilyProposition D :=
  forall_congr' fun i => At.proposition_families_iff D.nd D.naut h5.2.2.1 hO i

theorem proposition_parameters_iff_reduced (D : D7) (hT : tieLab D) : Conclusion42 D ↔ ReducedParameterProposition D :=
  forall_congr' fun i => parameter_proposition_iff D.nd D.naut hT i

theorem galois_clause_iff_reduced (D : D7) : ConclusionG5 D ↔ ReducedGaloisClause D :=
  forall_congr' fun i => At.galois_clause_iff_reduced D.nd D.naut i (Del_holds D i)

theorem galois_clause_of_sufficient (D : D7) (h : AdmA D) (ho : SufficientGaloisClause D) : ConclusionG5 D := fun i =>
  At.galois_clause_of_sufficient D.nd D.naut h.2.2.2.2.2.2.2.2.1 h.1.2.2 h.2.2.2.2.2.1 i (Del_holds D i) (ho i)

end Formalism.MainNotions.SumRepresentations
