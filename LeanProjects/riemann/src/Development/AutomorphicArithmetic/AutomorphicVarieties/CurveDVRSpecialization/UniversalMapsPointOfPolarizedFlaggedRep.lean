import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameCondition
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.OfForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ExistsDeterminantPairMapOfAlgHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.FlagRel

set_option linter.overlappingInstances false

section SlopeTestRemainingChoices

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.W UpperTheory.V.CA UpperTheory.V.AlgebraTools.Det

namespace UpperTheory.V.Pr

private theorem tr_single {n : ℕ} {A G K : Type} [CommRing A] [Group G] [CommRing K] (hn : 0 < n) (D : GDet n A G)
    (f : A →+* K) (ρ : G →* Matrix (Fin n) (Fin n) K) (h : D.map f = GDet.ofRep ρ) (g : G) :
    f (D.tr (MonoidAlgebra.single g 1)) = (ρ g).trace := by
  have h1 := ((d_gmap D).2.2.1 f (MonoidAlgebra.single g 1)).2 1
  rw [h, MonoidAlgebra.mapRingHom_single, map_one] at h1
  have h2 := (repApi ρ).2.2.1 hn (MonoidAlgebra.single g 1)
  rw [GDet.tr, h1] at h2
  rw [GDet.tr, h2]
  congr 1
  ext i j; simp [GDet.repAlg]

private theorem prod_smul {K : Type} [CommRing K] {M : Type} [Ring M] [Algebra K M] :
    ∀ {m : ℕ} (c : Fin m → K) (x : Fin m → M), (List.ofFn fun i => c i • x i).prod = (∏ i, c i) • (List.ofFn x).prod
  | 0, _, _ => by simp
  | m + 1, c, x => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Fin.prod_univ_succ,
      prod_smul (fun i => c i.succ) (fun i => x i.succ), smul_mul_smul_comm]

section Cont

variable {Γ Γ' R R' : Type} [TopologicalSpace Γ] [TopologicalSpace Γ'] [CommRing R] [CommRing R']

private theorem ac_mul {I : Ideal R} {f g : Γ → R} (hf : AdicCont I f) (hg : AdicCont I g) :
    AdicCont I fun x => f x * g x := fun N => by
  simp only [map_mul]
  exact (hf N).mul (hg N)

private theorem ac_comp {I : Ideal R} {f : Γ → R} (hf : AdicCont I f) {u : Γ' → Γ} (hu : Continuous u) :
    AdicCont I fun x => f (u x) := fun N => (hf N).comp_continuous hu

private theorem ac_map [IsLocalRing R] [IsLocalRing R'] (φ : R →+* R') [IsLocalHom φ] {f : Γ → R}
    (hf : AdicCont (maximalIdeal R) f) : AdicCont (maximalIdeal R') fun x => φ (f x) := fun N => by
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap φ :=
    le_trans (Ideal.pow_right_mono (fun y hy => map_nonunit φ y hy) N) (Ideal.le_comap_pow _ N)
  exact (hf N).comp (Ideal.quotientMap _ φ hle)

private theorem ac_desc {I : Ideal R} {f : Γ → R} {u : Γ' → Γ} (hu : Topology.IsQuotientMap u)
    (hf : AdicCont I fun x => f (u x)) : AdicCont I f := fun N s =>
  hu.isOpen_preimage.1 (hf N s)

end Cont

section Tw

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
  {F : Frame l (ResidueField O)} {n : ℕ} {G : GFrame l} {r : Resid G O n} (L : TwLink F r)

private theorem κ_map {C K : Type} [CommRing C] [Algebra O C] [CommRing K] [Algebra O K] (j : C →ₐ[O] K) (g : G.G₀) :
    j ((L.κA C g : Cˣ) : C) = (L.κA K g : Kˣ) := j.commutes _

private theorem κ_map_inv {C K : Type} [CommRing C] [Algebra O C] [CommRing K] [Algebra O K] (j : C →ₐ[O] K)
    (g : G.G₀) : j (((L.κA C g)⁻¹ : Cˣ) : C) = ((L.κA K g)⁻¹ : Kˣ) := by
  rw [← map_inv, ← map_inv, κ_map]

variable {C : Type} [CommRing C] [Algebra O C] [IsCO O C] (p : Pair r C)

private noncomputable def tt (g : G.G₀) : C := (((L.κA C g)⁻¹ : Cˣ) : C) * p.D.tr (MonoidAlgebra.single g 1)

private theorem κinv_cont : AdicCont (maximalIdeal C) fun g : G.G₀ => (((L.κA C g)⁻¹ : Cˣ) : C) := by
  have := ac_map (algebraMap O C) (ac_comp L.κ_cont continuous_inv)
  simp only [← map_inv]
  exact this

private theorem tt_cont : AdicCont (maximalIdeal C) (tt L p) := ac_mul (κinv_cont L) (p.cont 1)

private theorem tt_map (hn : 0 < n) {K : Type} [CommRing K] [Algebra O K] (j : C →ₐ[O] K)
    (r0 : G.G₀ →* Matrix (Fin n) (Fin n) K) (h : p.D.map (j : C →+* K) = GDet.ofRep r0) (g : G.G₀) :
    j (tt L p g) = (((L.κA K g)⁻¹ : Kˣ) : K) * (r0 g).trace := by
  rw [tt, map_mul, κ_map_inv, ← tr_single hn p.D _ r0 h]
  rfl

private theorem tt_res (hn : 0 < n) (g : G.G₀) :
    res O C (tt L p g) = ∑ i, ((F.Ψ (L.π g) ^ w n i : (ResidueField O)ˣ) : ResidueField O) := by
  rw [tt_map L p hn (res O C) _ p.red]
  show _ * (diagonal _).trace = _
  rw [trace_diagonal, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [L.chib, ← Units.val_mul]
  congr 1
  show (L.κA _ g)⁻¹ * (_ * L.κA _ g) = _
  rw [mul_comm _ (L.κA _ g), inv_mul_cancel_left]

private theorem π_quot : Topology.IsQuotientMap L.π := by
  haveI : CompactSpace G.G₀ := isCompact_iff_compactSpace.1 (G.η.ker.isClosed_of_isOpen G.η_open).isCompact
  exact L.π_cont.isClosedMap.isQuotientMap L.π_cont L.π_surj

private theorem chi_ex : ∃ χ : ∀ v, Fin n → F.Gv v →* Cˣ, IsPsi O F n (fun v i g => (χ v i g : C)) ∧
    ∀ v i g, χ (L.e v) i (L.lam v g) * L.κA C (G.φ v g) = p.ψ v i g := by
  have key : ∀ v : F.V, ∃ χ : Fin n → F.Gv v →* Cˣ, (∀ i, AdicCont (maximalIdeal C) (fun g => (χ i g : C)) ∧
      ∀ g, res O C (χ i g) = ((F.Ψ (F.loc v g) ^ w n i : (ResidueField O)ˣ) : ResidueField O)) ∧
      ∀ u (h : L.e u = v) i g, χ i (h ▸ L.lam u g) * L.κA C (G.φ u g) = p.ψ u i g := fun v => by
    obtain ⟨u, rfl⟩ := L.e.surjective v
    refine ⟨fun i => (p.ψ u i * ((L.κA C).comp (G.φ u))⁻¹).comp (L.lam u).symm.toMulEquiv.toMonoidHom,
      fun i => ⟨?_, fun g => ?_⟩, fun u' h i g => ?_⟩
    · exact ac_comp (ac_mul (p.psi u i).cont (ac_comp (κinv_cont L) (G.φ_cont u))) (L.lam u).symm.continuous
    · obtain ⟨g, rfl⟩ := (L.lam u).surjective g
      have h1 : (L.lam u).symm.toMulEquiv.toMonoidHom (L.lam u g) = g := (L.lam u).symm_apply_apply g
      rw [MonoidHom.comp_apply, h1]
      show res O C ((p.ψ u i g : Cˣ) * (((L.κA C (G.φ u g))⁻¹ : Cˣ) : C)) = _
      rw [map_mul, κ_map_inv, (p.psi u i).red, L.psib, L.chib, ← Units.val_mul, ← L.lam_loc]
      congr 1
      exact mul_inv_cancel_right _ _
    · obtain rfl := L.e.injective h
      have h1 : (L.lam u').symm.toMulEquiv.toMonoidHom (L.lam u' g) = g := (L.lam u').symm_apply_apply g
      rw [MonoidHom.comp_apply, h1]
      exact inv_mul_cancel_right _ _
  choose χ h1 h2 using key
  exact ⟨χ, h1, fun v i g => h2 _ v rfl i g⟩

end Tw

private theorem irr_conj {G K : Type} [Group G] [Field K] {n : ℕ} (r : G →* GL (Fin n) K)
    (a : G → Matrix (Fin n) (Fin n) K) (h : GL (Fin n) K) (H : ∀ g, a g = h * mat r g * h⁻¹) (hr : Af.IsIrr r) :
    MatIrr ⊤ a := by
  intro W hW
  have e : ∀ g, (h : Matrix (Fin n) (Fin n) K) * (r g : Matrix (Fin n) (Fin n) K) = a g * h := fun g => by
    rw [H, Units.inv_mul_cancel_right]; rfl
  rcases hr.2.2 (W.comap (Matrix.toLin' (h : Matrix (Fin n) (Fin n) K))) le_top (fun g v hv => by
    rw [Submodule.mem_comap, Matrix.toLin'_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec]
    exact hW g (Subgroup.mem_top g) _ hv) with h0 | h0
  · refine Or.inl (eq_bot_iff.2 fun v hv => ?_)
    have h1 : ((h⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v ∈
        W.comap (Matrix.toLin' (h : Matrix (Fin n) (Fin n) K)) := by
      rw [Submodule.mem_comap, Matrix.toLin'_apply, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      exact hv
    rw [h0, Submodule.mem_bot] at h1
    have h2 := congrArg ((h : Matrix (Fin n) (Fin n) K) *ᵥ ·) h1
    simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.mulVec_zero] at h2
    exact h2
  · refine Or.inr (eq_top_iff.2 fun v _ => ?_)
    have h1 : ((h⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v ∈
        W.comap (Matrix.toLin' (h : Matrix (Fin n) (Fin n) K)) := h0 ▸ Submodule.mem_top
    rwa [Submodule.mem_comap, Matrix.toLin'_apply, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at h1

private theorem main {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsCoef l O] [Algebra ℤ_[l] O] {F : Frame l (ResidueField O)} {n : ℕ} (T : Setup F n)
    {C : Type} [CommRing C] [Algebra O C] [IsCO O C] (p : Pair T.r C) {K : Type} [Field K]
    [IsAlgClosed K] [Algebra O K] (j : C →ₐ[O] K) (hj : Function.Injective j)
    (r : F.G0 →* GL (Fin n) K) (Q : GL (Fin n) K) (hQ : (Q : Matrix (Fin n) (Fin n) K)ᵀ = Q)
    (hform : ∀ g, (r g : Matrix (Fin n) (Fin n) K)ᵀ * (Q : Matrix (Fin n) (Fin n) K) *
      (r (F.conj g) : Matrix (Fin n) (Fin n) K) = Q)
    (h0 : p.D.map (j : C →+* K) = GDet.ofRep (mat (Af.tw (r.comp T.K.π) (T.K.κA K))))
    (hfl : ∀ v, HasFlag ((Af.tw (r.comp T.K.π) (T.K.κA K)).comp (T.G.φ v)) fun i => pushCh (j : C →+* K) (p.ψ v i))
    (hirr : Af.IsIrr r) :
    ∃ ρ' : NRep F n K, MatIrr ⊤ ρ'.r ∧ p.D.map (j : C →+* K) = GDet.ofRep (T.K.tw ρ') := by
  have hn : 0 < n := by have := T.n23; omega
  letI : Algebra C K := (j : C →+* K).toAlgebra
  have hv : ∀ g, mat (Af.tw (r.comp T.K.π) (T.K.κA K)) g = ((T.K.κA K g : Kˣ) : K) • mat r (T.K.π g) :=
    fun g => Af.tw_val _ _ g
  obtain ⟨χ, hχ, hψ⟩ := chi_ex T.K p
  have hb : ∀ g, j (tt T.K p g) = (mat r (T.K.π g)).trace := fun g => by
    rw [tt_map T.K p hn j _ h0, hv, trace_smul, smul_eq_mul, Units.inv_mul_cancel_left]
  let t : F.G0 → C := fun x => tt T.K p (Function.surjInv T.K.π_surj x)
  have ht0 : ∀ x, j (t x) = (mat r x).trace := fun x => by
    have := hb (Function.surjInv T.K.π_surj x)
    rwa [Function.surjInv_eq T.K.π_surj] at this
  have ht : ∀ g, t (T.K.π g) = tt T.K p g := fun g => hj (by rw [ht0, hb])
  have hψ' : ∀ v i g, j (p.ψ v i g : Cˣ) =
      (T.K.κA K (T.G.φ v g) : Kˣ) * j (χ (T.K.e v) i (T.K.lam v g) : Cˣ) := fun v i g => by
    rw [← hψ, Units.val_mul, map_mul, mul_comm, ← κ_map T.K j]
  refine Exists.elim (of_form T.ok T.n23 C K hj (mat r) Q t χ Q.isUnit hQ hform ⟨?_, fun x => ?_⟩ ht0 hχ
    (fun v g => ?_)) fun ρ H => ?_
  · refine ac_desc (π_quot T.K) ?_
    simp only [ht]
    exact tt_cont T.K p
  · obtain ⟨g, rfl⟩ := T.K.π_surj x
    rw [ht, tt_res T.K p hn]
  · obtain ⟨u, rfl⟩ := T.K.e.surjective v
    obtain ⟨g, rfl⟩ : ∃ g' : Fin n → T.G.Gv u, g = fun i => T.K.lam u (g' i) :=
      ⟨fun i => (T.K.lam u).symm (g i), funext fun i => ((T.K.lam u).apply_symm_apply _).symm⟩
    have h1 := (flagRel _ _ (hfl u)).2 g
    have h2 := prod_smul (fun i => ((T.K.κA K (T.G.φ u (g i)) : Kˣ) : K))
      (fun i => mat r (F.loc0 _ (T.K.lam u (g i))) -
        j (χ (T.K.e u) i (T.K.lam u (g i)) : Cˣ) • (1 : Matrix (Fin n) (Fin n) K))
    have h3 := h2.symm.trans (Eq.trans (congrArg (fun f => (List.ofFn f).prod) (funext fun i => by
      rw [smul_sub, T.K.lam_loc, ← hv, smul_smul, ← hψ']
      rfl)) h1)
    exact (IsUnit.smul_eq_zero (IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun i _ => Units.ne_zero _))).1 h3
  · obtain ⟨h, H1, -, -⟩ := H
    refine ⟨ρ, irr_conj r _ h H1 hirr, h0.trans ((repApi _).2.2.2.2.2.2.2 _ h fun g => ?_)⟩
    show _ = (((T.K.κA K g : Kˣ) : K) • ρ.r (T.K.π g)) * _
    rw [hv, H1, mul_smul_comm, smul_mul_assoc, Units.inv_mul_cancel_right]

end UpperTheory.V.Pr

end SlopeTestRemainingChoices

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr
open scoped Matrix

theorem UpperTheory.universalMaps_point_of_polarized_flagged_rep :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Fr.IsCoef l O] [Algebra ℤ_[l] O] {F : Fr.Frame l (ResidueField O)} {n : ℕ} (T : Setup F n) (K' : Type) [Field K'] [IsAlgClosed K'] [Algebra O K'] (x : T.B.B →ₐ[O] K') (r : F.G0 →* GL (Fin n) K') (ρ : T.G.G₀ →* GL (Fin n) K') (Q : GL (Fin n) K') (ψ : ∀ v, Fin n → T.G.Gv v →* K'ˣ), (Q : Matrix (Fin n) (Fin n) K')ᵀ = Q → (∀ g, (r g : Matrix (Fin n) (Fin n) K')ᵀ * (Q : Matrix (Fin n) (Fin n) K') * (r (F.conj g) : Matrix (Fin n) (Fin n) K') = Q) → ρ = tw (r.comp T.K.π) (T.K.κA K') → T.B.u.Maps (x : T.B.B →+* K') (W.GDet.ofRep (W.mat ρ)) ψ → (∀ v, W.HasFlag (ρ.comp (T.G.φ v)) (ψ v)) → IsIrr r → ∃ ρ' : Fr.NRep F n K', MatIrr ⊤ ρ'.r ∧ T.B.u.D.map (x : T.B.B →+* K') = W.GDet.ofRep (T.K.tw ρ') := by
  intro l _ O _ _ _ _ _ F n T K' _ _ _ x r ρ Q ψ hQ hform hρ hx hfl hirr
  subst hρ
  haveI : Alg.IsCO O x.range := Alg.co_quot O _ _ x.rangeRestrict x.rangeRestrict_surjective
  obtain ⟨p, hp⟩ := W.exists_determinantPair_map_of_algHom l T.G O n T.r T.B.B x.range x.rangeRestrict T.B.u
  have hD : p.D.map (x.range.val : x.range →+* K') = T.B.u.D.map (x : T.B.B →+* K') := by
    rw [← hp.1, (CA.d_gmap _).2.1]; rfl
  rw [← hD]
  refine main T p x.range.val Subtype.val_injective r Q hQ hform (hD.trans hx.1) (fun v => ?_) hirr
  have : (fun i => W.pushCh (x.range.val : x.range →+* K') (p.ψ v i)) = ψ v := funext fun i => by
    rw [← hp.2 v i, ← hx.2 v i]; rfl
  rw [this]
  exact hfl v
