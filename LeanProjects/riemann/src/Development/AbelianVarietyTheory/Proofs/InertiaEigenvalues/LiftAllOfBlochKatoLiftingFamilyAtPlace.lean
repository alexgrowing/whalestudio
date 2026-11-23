import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocMulVec
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Pass.LocDirect

theorem isSubFam_of_fintype {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {ι : Type} {k : ℕ} (Ms : ι → (G →* Matrix (Fin k) (Fin k) LL)) (W : GRep G Qp LL O)
    {κ : Type} [Fintype κ] (x : κ → ι) (p : κ → W.V →ₗ[LL] (Fin k → LL))
    (h1 : ∀ j g v, p j (W.ρ g v) = (Ms (x j) g).mulVec (p j v)) (h2 : ∀ v, (∀ j, p j v = 0) → v = 0) :
    IsSubFam Ms W := by
  classical
  let e := Fintype.equivFin κ
  refine ⟨Fintype.card κ, fun m => x (e.symm m), fun m => p (e.symm m), fun m g v => h1 _ g v,
    fun v hv => h2 v fun j => ?_⟩
  simpa using hv (e j)

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem loc_eq_map {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw) :
    Br.loc D.nbr i w hw M g =
      (mapM (toK D.nd i) M ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd)).map (Br.toLLK (D.nbr i w hw)) := by
  ext a b
  simp only [Br.loc, Br.locM, Br.locO, mapM, MonoidHom.coe_comp, Function.comp_apply, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply, toK]
  exact congrArg Subtype.val (Br.toLLK_alg (D.nbr i w hw) _).symm

end GlobalTheory.Pass.LocDirect

namespace GlobalTheory.Pass.LocDirect

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem exists_locEmb (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) {k : ℕ}
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (x₀ : D.nd.X i)
    (j : (Fin k → KK D.nd i) →ₗ[KK D.nd i] (Fin D.R.nV → KK D.nd i)) (hj : Function.Injective j)
    (hjM : ∀ g v, j ((mapM (toK D.nd i) M g).mulVec v) = (mapM (toK D.nd i) (rTwO D.nd i r x₀) g).mulVec (j v)) :
    ∃ J : Matrix (Fin D.R.nV) (Fin k) (Br.LL D.nbr i w hw),
      (∀ v, J.mulVec v = 0 → v = 0) ∧
      ∀ g, J * Br.loc D.nbr i w hw M g = Br.loc D.nbr i w hw (rTwO D.nd i r x₀) g * J := by
  classical
  obtain ⟨l, hl⟩ := LinearMap.exists_leftInverse_of_injective j (LinearMap.ker_eq_bot.mpr hj)
  have hLJ : LinearMap.toMatrix' l * LinearMap.toMatrix' j = 1 := by
    rw [← LinearMap.toMatrix'_comp, hl, LinearMap.toMatrix'_id]
  have hJM : ∀ γ, LinearMap.toMatrix' j * mapM (toK D.nd i) M γ =
      mapM (toK D.nd i) (rTwO D.nd i r x₀) γ * LinearMap.toMatrix' j := by
    intro γ
    have e : j ∘ₗ Matrix.toLin' (mapM (toK D.nd i) M γ) =
        Matrix.toLin' (mapM (toK D.nd i) (rTwO D.nd i r x₀) γ) ∘ₗ j := by
      refine LinearMap.ext fun v => ?_
      rw [LinearMap.comp_apply, LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, hjM]
    have := congrArg LinearMap.toMatrix' e
    simpa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] using this
  set f := Br.toLLK (D.nbr i w hw)
  refine ⟨(LinearMap.toMatrix' j).map f, fun v hv => ?_, fun g => ?_⟩
  · have h1 : ((LinearMap.toMatrix' l).map f * (LinearMap.toMatrix' j).map f) = 1 := by
      rw [← Matrix.map_mul, hLJ, Matrix.map_one _ (map_zero f) (map_one f)]
    calc v = ((LinearMap.toMatrix' l).map f * (LinearMap.toMatrix' j).map f).mulVec v := by
          rw [h1, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  · rw [loc_eq_map, loc_eq_map, ← Matrix.map_mul, ← Matrix.map_mul, hJM]

end GlobalTheory.Pass.LocDirect

namespace GlobalTheory.Pass.LocDirect

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem isSubFam_of_isSubSumOf (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i))
    {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hSub : SubTw i r Xs M)
    (hM : Continuous fun g => M g) {a : ℕ} (x : Fin a → D.nd.X i) (hx : ∀ j, x j ∈ Xs)
    (hc : ∀ j, Continuous fun g => Br.loc D.nbr i w hw (rTwO D.nd i r (x j)) g)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y,
      (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y)
    (Wr : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw))
    (h : BlochKatoDuality.IsSubSumOf Wr.ρ (Xgrep i w hw r x hc Y hst).ρ (ModuleGaloisRepresentation i w hw M hM).ρ) :
    IsSubFam (fun x : ↥Xs => Br.loc D.nbr i w hw (rTwO D.nd i r x)) Wr := by
  classical
  obtain ⟨-, x₀, hx₀, j, hj, hjM⟩ := hSub
  obtain ⟨J, hJi, hJ⟩ := exists_locEmb i w hw r M x₀ j hj hjM
  obtain ⟨a', b', p, q, hp, hq, hinj⟩ := h
  let cX : Fin a → (↥(XV i w hw Y) →ₗ[Br.LL D.nbr i w hw] (Fin D.R.nV → Br.LL D.nbr i w hw)) :=
    fun m => LinearMap.proj m ∘ₗ (XV i w hw Y).subtype
  let P : (Fin a' × Fin a) ⊕ Fin b' → Wr.V →ₗ[Br.LL D.nbr i w hw] (Fin D.R.nV → Br.LL D.nbr i w hw) :=
    Sum.elim (fun ij => cX ij.2 ∘ₗ (p ij.1 : Wr.V →ₗ[Br.LL D.nbr i w hw] ↥(XV i w hw Y)))
      (fun m => Matrix.mulVecLin J ∘ₗ (q m : Wr.V →ₗ[Br.LL D.nbr i w hw] (Fin k → Br.LL D.nbr i w hw)))
  let xf : (Fin a' × Fin a) ⊕ Fin b' → ↥Xs := Sum.elim (fun ij => ⟨x ij.2, hx ij.2⟩) (fun _ => ⟨x₀, hx₀⟩)
  refine isSubFam_of_fintype _ Wr xf P ?_ ?_
  · rintro (⟨m, n⟩ | m) g v
    · have e1 := hp m g v
      change cX n (p m (Wr.ρ g v)) = (Br.loc D.nbr i w hw (rTwO D.nd i r (x n)) g).mulVec (cX n (p m v))
      rw [e1]
      rfl
    · have e1 := hq m g v
      change J.mulVec (q m (Wr.ρ g v)) = (Br.loc D.nbr i w hw (rTwO D.nd i r x₀) g).mulVec (J.mulVec (q m v))
      rw [e1]
      have key : ∀ u : Fin k → Br.LL D.nbr i w hw, J.mulVec ((Br.loc D.nbr i w hw M g).mulVec u) =
          (Br.loc D.nbr i w hw (rTwO D.nd i r x₀) g).mulVec (J.mulVec u) := fun u => by
        rw [Matrix.mulVec_mulVec, hJ, ← Matrix.mulVec_mulVec]
      exact key (q m v)
  · intro v hv
    refine hinj v (fun m => ?_) (fun m => hJi _ (hv (Sum.inr m)))
    apply Subtype.ext
    funext n
    exact hv (Sum.inl (m, n))

end GlobalTheory.Pass.LocDirect

namespace GlobalTheory.Pass.LocDirect

theorem liftAll_of_liftFamW : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))),
    GoodR D.nd i r → ∀ (Xs : Set (D.nd.X i)) (e : ℕ), LiftFamW i w hw (fun x : ↥Xs => rTwO D.nd i r x) e →
    ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)), SubTw i r Xs M →
    ∀ (hM : Continuous fun g => M g) (a : ℕ) (x : Fin a → D.nd.X i), (∀ j, x j ∈ Xs) →
    ∀ (hc : ∀ j, Continuous fun g => Br.loc D.nbr i w hw (rTwO D.nd i r (x j)) g)
      (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
      (hst : (∀ γ : GE D.nd, ∀ y ∈ Y,
        (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y)),
    BlochKatoDuality.LiftAll (Br.PD D.loc D.nbr i w hw) (GlobalTheory.Pass.LocDirect.Xgrep i w hw r x hc Y hst)
      (GlobalTheory.Pass.LocDirect.ModuleGaloisRepresentation i w hw M hM) e := by
  intro D i w hw r _ Xs e hL k M hSub hM a x hx hc Y hst W₁ W₂ h₁ h₂ L₁ L₂ F hF
  exact hL W₁ W₂ (isSubFam_of_isSubSumOf i w hw r Xs M hSub hM x hx hc Y hst W₁ h₁)
    (isSubFam_of_isSubSumOf i w hw r Xs M hSub hM x hx hc Y hst W₂ h₂) L₁ L₂ F hF

end GlobalTheory.Pass.LocDirect
