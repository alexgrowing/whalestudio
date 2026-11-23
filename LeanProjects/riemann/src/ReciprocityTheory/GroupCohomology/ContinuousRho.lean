import ReciprocityTheory.GroupCohomology.CardLenStatement
import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB
import ReciprocityTheory.GroupCohomology.ResNormalHolds
import ReciprocityTheory.GroupCohomology.InnerHolds

namespace ReciprocityTheory.Coh

namespace QuadraticConjugation

open ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def conjHom (U : Subgroup G) [U.Normal] (s : G) : U →* U where
  toFun g := ⟨s⁻¹ * g * s, by simpa using ‹U.Normal›.conj_mem g g.2 s⁻¹⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

@[simp] theorem conjHom_coe (U : Subgroup G) [U.Normal] (s : G) (g : U) :
    ((conjHom U s g : U) : G) = s⁻¹ * g * s := rfl

theorem continuous_rho' (N : TRep R G) (s : G) : Continuous (N.rho s) :=
  N.cont.comp (f := fun m : N.V => (s, m)) (continuous_const.prodMk continuous_id)

theorem rho_conj (N : TRep R G) (s g : G) (m : N.V) :
    N.rho s (N.rho (s⁻¹ * g * s) m) = N.rho g (N.rho s m) := by
  have : s * (s⁻¹ * g * s) = g * s := by group
  rw [← Module.End.mul_apply, ← map_mul, this, map_mul, Module.End.mul_apply]

def conjPair (N : TRep R G) (U : Subgroup G) [U.Normal] (s : G) : Pair (N.resSub U) (N.resSub U) where
  φ := conjHom U s
  u := N.rho s
  φ_cont := Continuous.subtype_mk
    ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  u_cont := continuous_rho' N s
  equiv g m := rho_conj N s g m

def conjG (s : G) : G →* G where
  toFun g := s⁻¹ * g * s
  map_one' := by simp
  map_mul' a b := by group

def innerPair (N : TRep R G) (s : G) : Pair N N where
  φ := conjG s
  u := N.rho s
  φ_cont := (continuous_const.mul continuous_id).mul continuous_const
  u_cont := continuous_rho' N s
  equiv g m := rho_conj N s g m

end

section Lemmas

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

end Lemmas

section Main

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M M' : TRep R G} {U : Subgroup G} [U.Normal] (P : Pair M' (M.resSub U))

theorem phi_apply (hφ : P.φ = U.subtype) (g : U) : P.φ g = (g : G) := by rw [hφ]; rfl

noncomputable def PU (hφ : P.φ = U.subtype) : Pair (M'.resSub U) (M.resSub U) where
  φ := MonoidHom.id U
  u := P.u
  φ_cont := continuous_id
  u_cont := P.u_cont
  equiv g m := by
    have := P.equiv g m
    rw [phi_apply P hφ] at this
    exact this

noncomputable def eqv (hP : IsHomeomorph P.u) : M'.V ≃ₗ[R] (M.resSub U).V := LinearEquiv.ofBijective P.u hP.bijective

theorem eqv_symm (hP : IsHomeomorph P.u) (m : (M.resSub U).V) : P.u ((eqv P hP).symm m) = m :=
  (eqv P hP).apply_symm_apply m

noncomputable def PInv (hφ : P.φ = U.subtype) (hP : IsHomeomorph P.u) : Pair (M.resSub U) (M'.resSub U) where
  φ := MonoidHom.id U
  u := (eqv P hP).symm.toLinearMap
  φ_cont := continuous_id
  u_cont := by
    have h1 : ∀ m, P.u ((hP.homeomorph P.u).symm m) = m := fun m =>
      (hP.homeomorph P.u).apply_symm_apply m
    refine (hP.homeomorph P.u).symm.continuous.congr fun m => hP.bijective.1 ?_
    show P.u _ = P.u ((eqv P hP).symm m)
    rw [h1, eqv_symm]
  equiv g m := by
    apply hP.bijective.1
    show P.u ((eqv P hP).symm ((M.resSub U).rho g m)) = P.u (M'.rho g ((eqv P hP).symm m))
    have := P.equiv g ((eqv P hP).symm m)
    rw [phi_apply P hφ] at this
    rw [this, eqv_symm, eqv_symm]

end Main

end QuadraticConjugation

end ReciprocityTheory.Coh
