import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom

namespace GlobalTheory.GlueUnique

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_proj {K M : Type} [Field K] [AddCommGroup M] [Module K M] (U : Submodule K M) :
    ∃ Q : M →ₗ[K] M, (∀ x ∈ U, Q x = 0) ∧ ∀ x, x - Q x ∈ U := by
  obtain ⟨W, hW⟩ := U.exists_isCompl
  refine ⟨LinearMap.id - U.subtype ∘ₗ U.projectionOnto W hW, fun x hx => ?_, fun x => ?_⟩
  · have := Submodule.linearProjOfIsCompl_apply_left hW ⟨x, hx⟩
    simp [this]
  · simp

theorem exists_lattice {O K : Type} [CommRing O] [Field K] [Algebra O K] {n : ℕ} (Λ : Submodule O (Fin n → K))
    (h : Λ.FG) : ∃ (Q : (Fin n → K) →ₗ[K] (Fin n → K)) (Λ' : Submodule O (Fin n → K)),
      Submodule.IsLattice K Λ' ∧ Λ ≤ Λ' ∧ (∀ x ∈ Λ, Q x = 0) ∧ ∀ x ∈ Λ', Q x = 0 → x ∈ Λ := by
  obtain ⟨Q, h1, h2⟩ := exists_proj (Submodule.span K (Λ : Set (Fin n → K)))
  have h3 : ∀ x, Q (Q x) = Q x := fun x => by
    have := h1 _ (h2 x)
    rw [map_sub, sub_eq_zero] at this
    exact this.symm
  refine ⟨Q, Λ ⊔ Submodule.span O (Set.range fun j : Fin n => Q (Pi.single j 1)), ⟨?_, ?_⟩, le_sup_left,
    fun x hx => h1 x (Submodule.subset_span hx), fun x hx h0 => ?_⟩
  · exact h.sup (Submodule.fg_span (Set.finite_range _))
  · rw [eq_top_iff, ← (Pi.basisFun K (Fin n)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [Pi.basisFun_apply, ← sub_add_cancel (Pi.single j 1 : Fin n → K) (Q (Pi.single j 1))]
    refine add_mem (Submodule.span_mono ?_ (h2 _)) (Submodule.subset_span ?_)
    · exact fun y hy => Submodule.mem_sup_left hy
    · exact Submodule.mem_sup_right (Submodule.subset_span ⟨j, rfl⟩)
  · obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    have h4 : Q b = b := by
      refine Submodule.span_induction (p := fun b _ => Q b = b) ?_ (map_zero Q) ?_ ?_ hb
      · rintro _ ⟨j, rfl⟩
        exact h3 _
      · intro x y _ _ hx hy
        rw [map_add, hx, hy]
      · intro c x _ hx
        rw [← algebraMap_smul K c x, map_smul, hx]
    rw [map_add, h1 a (Submodule.subset_span ha), h4, zero_add] at h0
    rwa [h0, add_zero]

theorem map_mulVec_gen {K A : Type} [CommRing K] [CommRing A] (f : K →+* A) {n : ℕ}
    (Q : (Fin n → K) →ₗ[K] (Fin n → K)) (x : Fin n → K) :
    (LinearMap.toMatrix' Q).map f *ᵥ (fun i => f (x i)) = fun i => f (Q x i) := by
  funext i
  rw [← LinearMap.toMatrix'_mulVec, RingHom.map_mulVec]
  rfl

variable {D : D7}

theorem inc_injective : Function.Injective (inc D) := by
  obtain ⟨P, hP, h0⟩ := Ring.exists_maximal_of_not_isField (RingOfIntegers.not_isField D.host.E) |>.imp fun _ h => h.symm
  intro a b hab
  have := congrArg (GlobalTheory.StdFrames.cpt (D := D) ⟨P, hP.isPrime, h0⟩) hab
  rw [cpt_inc, cpt_inc] at this
  exact (algebraMap D.host.E _).injective this

theorem mem_of_inc_mem_hat {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (h : Λ.FG)
    {x : Fin n → D.host.E} (hx : (fun i => inc D (x i)) ∈ hat Λ) : x ∈ Λ := by
  obtain ⟨Q, Λ', h1, h2, h3, h4⟩ := exists_lattice Λ h
  refine h4 x ((inc_mem_hat_iff h1 x).1 (hat_mono h2 hx)) ?_
  have h5 : (LinearMap.toMatrix' Q).map (inc D) *ᵥ (fun i => inc D (x i)) = 0 := by
    refine hat_induction (p := fun y => (LinearMap.toMatrix' Q).map (inc D) *ᵥ y = 0) ?_ (mulVec_zero _) ?_ ?_ hx
    · intro y hy
      rw [map_mulVec_gen, h3 y hy]
      funext i
      exact RingHom.map_zero _
    · intro a b ha hb
      rw [mulVec_add, ha, hb, add_zero]
    · intro a _ b hb
      rw [mulVec_smul, hb, smul_zero]
  rw [map_mulVec_gen] at h5
  funext i
  exact inc_injective ((congrFun h5 i).trans (RingHom.map_zero _).symm)

theorem inCmp_iff {u : D.what₂.Word} {π : 𝓞 D.host.E} (hπ : IsPi u π) {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V}
    {z : Y.V} {L₀ : Lat X} {f₀ : Pl D.host.E → Fin X.rank → EAf D} {L L' : Submodule (𝓞 D.host.E) Y.V}
    (h : IsGlued Y X ι z u π L₀ f₀ L) (h' : IsGlued Y X ι z u π L₀ f₀ L') (w : Pl D.host.E) (y : Fin Y.rank → EAf D) :
    InCmp (idem w) (Formalism.L2.Herm.crdLat Y L) y ↔ InCmp (idem w) (Formalism.L2.Herm.crdLat Y L') y := by
  by_cases hT : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal
  · rcases (T_mem_iff hπ w).1 hT with hw | hw
    · exact ((h.2.2 w _ (isPlIdem_idem w) hw).1 y).trans ((h'.2.2 w _ (isPlIdem_idem w) hw).1 y).symm
    · have a := h.2.2 _ _ (isPlIdem_idem _) hw
      have a' := h'.2.2 _ _ (isPlIdem_idem _) hw
      rw [cjA_idem, GlobalTheory.StdFrames.cP_cP] at a a'
      refine (a.2 y).trans (Iff.trans ?_ (a'.2 y).symm)
      refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun y' => ?_
      rw [a.1 y', a'.1 y']
  · exact (h.2.1 w _ (isPlIdem_idem w) hT y).trans (h'.2.1 w _ (isPlIdem_idem w) hT y).symm

theorem glued_le {u : D.what₂.Word} {π : 𝓞 D.host.E} (hπ : IsPi u π) {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V}
    {z : Y.V} {L₀ : Lat X} {f₀ : Pl D.host.E → Fin X.rank → EAf D} {L L' : Submodule (𝓞 D.host.E) Y.V}
    (h : IsGlued Y X ι z u π L₀ f₀ L) (h' : IsGlued Y X ι z u π L₀ f₀ L') : L ≤ L' := by
  intro x hx
  have hfg : (Formalism.L2.Herm.crdLat Y L').FG := h'.1.map _
  have h1 : vA Y x ∈ hat (Formalism.L2.Herm.crdLat Y L') := mem_hat_of_idem hfg fun w =>
    ((inCmp_iff hπ h h' w _).1 ⟨smul_mem_hat (idem_mem w) (vA_mem_hat Y hx), by rw [smul_smul, idem_mul_self]⟩).1
  obtain ⟨x', hx', e⟩ := mem_of_inc_mem_hat hfg h1
  rwa [← (Formalism.L2.Herm.crd Y).injective e]

theorem glued_unique (D : D7) (u : D.what₂.Word) (π : 𝓞 D.host.E) (hπ : IsPi u π) (Y X : HSp D)
    (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V) (L₀ : Lat X) (f₀ : Pl D.host.E → Fin X.rank → EAf D)
    (L L' : Submodule (𝓞 D.host.E) Y.V) (h : IsGlued Y X ι z u π L₀ f₀ L) (h' : IsGlued Y X ι z u π L₀ f₀ L') :
    L = L' :=
  le_antisymm (glued_le hπ h h') (glued_le hπ h' h)

end GlobalTheory.GlueUnique

end
