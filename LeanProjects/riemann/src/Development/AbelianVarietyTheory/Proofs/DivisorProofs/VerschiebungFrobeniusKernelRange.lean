import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniquePairsToTower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneRanksFieldCharPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneModulesFreeFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPullbackBasisStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct IsLocalRing

namespace GlobalTheory

namespace PDiv

theorem ker_le_range_of_residueField {R A B C A' B' C' : Type} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [AddCommGroup A] [Module R A] [Module.Finite R A]
    [AddCommGroup B] [Module R B] [Module.Free R B] [AddCommGroup C] [Module R C]
    [AddCommGroup A'] [Module (ResidueField R) A'] [AddCommGroup B'] [Module (ResidueField R) B']
    [AddCommGroup C'] [Module (ResidueField R) C'] (f : A →ₗ[R] B) (g : C →ₗ[R] A)
    (f' : A' →ₗ[ResidueField R] B') (g' : C' →ₗ[ResidueField R] A')
    (a : A →ₛₗ[algebraMap R (ResidueField R)] A') (b : B →ₛₗ[algebraMap R (ResidueField R)] B')
    (c : C →ₛₗ[algebraMap R (ResidueField R)] C') (hfg : ∀ z, f (g z) = 0)
    (hf : ∀ x, b (f x) = f' (a x)) (hg : ∀ z, a (g z) = g' (c z))
    (ha : Function.Injective (liftSemi a)) (hc : Function.Surjective (liftSemi c))
    (h : LinearMap.ker f' ≤ LinearMap.range g') : LinearMap.ker f ≤ LinearMap.range g := by
  have hc' : Function.Surjective c := fun z' => by
    obtain ⟨t, rfl⟩ := hc z'
    induction t with
    | zero => exact ⟨0, (map_zero c).trans (map_zero _).symm⟩
    | add s t hs ht =>
      obtain ⟨x, hx⟩ := hs
      obtain ⟨y, hy⟩ := ht
      exact ⟨x + y, by rw [map_add, map_add, hx, hy]⟩
    | tmul r z =>
      obtain ⟨r, rfl⟩ := residue_surjective r
      exact ⟨r • z, by rw [map_smulₛₗ, liftSemi_tmul]; rfl⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal R)
    (IsNoetherian.noetherian _) (maximalIdeal_le_jacobson _) fun x hx => ?_
  obtain ⟨z', hz'⟩ := h (show f' (a x) = 0 by rw [← hf, LinearMap.mem_ker.1 hx, map_zero])
  obtain ⟨z, rfl⟩ := hc' z'
  have h₁ : (1 : ResidueField R) ⊗ₜ[R] (x - g z) = 0 := ha (by
    rw [liftSemi_tmul, map_sub, hg, hz', sub_self, smul_zero, map_zero])
  have h₂ : x - g z ∈ maximalIdeal R • (⊤ : Submodule R A) := by
    rw [← LinearMap.ker_tensorProductMk]
    exact h₁
  rw [hϖ.maximalIdeal_eq, Submodule.ideal_span_singleton_smul] at h₂
  obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h₂
  have h₃ : f y = 0 := by
    have e : ϖ • f y = 0 := by
      rw [← map_smul, hy, map_sub, hfg, LinearMap.mem_ker.1 hx, sub_self]
    exact (smul_eq_zero.1 e).resolve_left hϖ.ne_zero
  rw [← sub_add_cancel x (g z), ← hy, add_comm]
  exact Submodule.add_mem_sup ⟨z, rfl⟩ (Submodule.smul_mem_smul hϖ.not_isUnit h₃)

end PDiv

namespace PDivGroup

open PDiv

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R]

theorem rigExtMap_hom_bijective {G H : PDivGroup p R} (e : G ≅ H) :
    Function.Bijective (rigExtMap e.hom) :=
  Function.bijective_iff_has_inverse.2 ⟨rigExtMap e.inv,
    fun x => by rw [← LinearMap.comp_apply, ← rigExtMap_comp, e.inv_hom_id, rigExtMap_id]; rfl,
    fun x => by rw [← LinearMap.comp_apply, ← rigExtMap_comp, e.hom_inv_id, rigExtMap_id]; rfl⟩

variable (h : (p : R) = 0) (G : PDivGroup p R)

theorem absFrob_rig_rigOfOmega (w : G.omega) : (absFrob h G).rig (G.rigOfOmega w) = 0 := by
  rw [← rigExtMap_relFrob_rig, SemiHom.rig_rigOfOmega]
  exact LinearMap.congr_fun (rigExtMap_relFrob_comp_rigOfOmega h G) _

theorem rigExtMap_verschiebung_absFrob_rig (x : G.RigExt) :
    rigExtMap (verschiebung h G) ((absFrob h G).rig x) = 0 := by
  rw [← (absFrob h (frobTwist h G)).rig_naturality (absFrob h G) (verschiebung h G)
    (verschiebung h G) (fun n a => by simp only [absFrob_app, map_pow])]
  obtain ⟨w, hw⟩ := range_rigExtMap_verschiebung_le h G ⟨x, rfl⟩
  rw [← hw, absFrob_rig_rigOfOmega]

theorem liftSemi_frobTwist_rig_bijective (S : Type) [CommRing S] [Algebra R S] (h' : (p : S) = 0)
    (hG : Module.Projective R (frobTwist h G).dual.omega) :
    Function.Bijective (liftSemi ((G.toBase S).frobTwist h h').rig) := by
  rw [← SemiHom.rigExtMap_lift_comp_liftSemi, LinearMap.coe_comp]
  exact (rigExtMap_hom_bijective (frobTwistBaseChange h G h')).comp
    (liftSemi_rig_bijective S _ h (Or.inr hG))

section Residue

variable [IsDomain R] [IsDiscreteValuationRing R] (h' : (p : ResidueField R) = 0)
  (bN : Function.Bijective (liftSemi (G.toBase (ResidueField R)).rig))
  (bM : Function.Bijective (liftSemi ((G.toBase (ResidueField R)).frobTwist h h').rig))

include bN bM

theorem ker_relFrob_le_of_residueField (_ : Module.Finite R (frobTwist h G).RigExt)
    (_ : Module.Free R G.RigExt)
    (k : LinearMap.ker (rigExtMap (relFrob h' (G.baseChange (ResidueField R)))) ≤
      LinearMap.range (rigExtMap (verschiebung h' (G.baseChange (ResidueField R))))) :
    LinearMap.ker (rigExtMap (relFrob h G)) ≤ LinearMap.range (rigExtMap (verschiebung h G)) :=
  ker_le_range_of_residueField _ _ _ _ ((G.toBase (ResidueField R)).frobTwist h h').rig
    (G.toBase (ResidueField R)).rig (G.toBase (ResidueField R)).rig
    (fun z => LinearMap.range_le_ker_iff.2 (rigExtMap_relFrob_comp_rigOfOmega h G)
      (range_rigExtMap_verschiebung_le h G ⟨z, rfl⟩))
    (SemiHom.rig_naturality _ _ _ _ ((G.toBase (ResidueField R)).app_relFrob h h'))
    (SemiHom.rig_naturality _ _ _ _ ((G.toBase (ResidueField R)).app_verschiebung h h'))
    bM.1 bN.2 k

theorem ker_verschiebung_le_of_residueField (_ : Module.Finite R G.RigExt)
    (_ : Module.Free R (frobTwist h G).RigExt)
    (e : ∀ z, rigExtMap (verschiebung h G) (rigExtMap (relFrob h G) z) = 0)
    (k : LinearMap.ker (rigExtMap (verschiebung h' (G.baseChange (ResidueField R)))) ≤
      LinearMap.range (rigExtMap (relFrob h' (G.baseChange (ResidueField R))))) :
    LinearMap.ker (rigExtMap (verschiebung h G)) ≤ LinearMap.range (rigExtMap (relFrob h G)) :=
  ker_le_range_of_residueField _ _ _ _ (G.toBase (ResidueField R)).rig
    ((G.toBase (ResidueField R)).frobTwist h h').rig ((G.toBase (ResidueField R)).frobTwist h h').rig
    e (SemiHom.rig_naturality _ _ _ _ ((G.toBase (ResidueField R)).app_verschiebung h h'))
    (SemiHom.rig_naturality _ _ _ _ ((G.toBase (ResidueField R)).app_relFrob h h'))
    bN.1 bM.2 k

end Residue

theorem range_relFrob_eq_span {ι : Type} (b : ι → G.RigExt)
    (hb : Submodule.span R (Set.range fun j => (frobProj h G).rig (b j)) = ⊤) :
    LinearMap.range (rigExtMap (relFrob h G)) =
      Submodule.span R (Set.range (absFrob h G).rig) := by
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · rw [LinearMap.range_eq_map (rigExtMap (relFrob h G)), ← hb, Submodule.map_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact ⟨_, (rigExtMap_relFrob_rig h G _).symm⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨_, rigExtMap_relFrob_rig h G x⟩

set_option maxHeartbeats 800000 in

theorem exact_frobenius_verschiebung_of_isDiscreteValuationRing
    (hW : Published.BarsottiTateDieudonne.WittModule) (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] (h : (p : R) = 0) (G : PDivGroup p R) :
    LinearMap.range (rigExtMap (verschiebung h G)) = LinearMap.range (frobTwist h G).rigOfOmega ∧
    LinearMap.ker (rigExtMap (relFrob h G)) = LinearMap.range (frobTwist h G).rigOfOmega ∧
    LinearMap.ker (rigExtMap (verschiebung h G)) = LinearMap.range (rigExtMap (relFrob h G)) ∧
    LinearMap.range (rigExtMap (relFrob h G)) =
      Submodule.span R (Set.range (absFrob h G).rig) := by
  obtain ⟨-, -, f₁, -, -, -, f₂, f₃⟩ := T.dieudonne_modules_free_finite hW p R h G
  obtain ⟨-, -, g₁, -, -, -, g₂, g₃⟩ := T.dieudonne_modules_free_finite hW p R h (frobTwist h G)
  have h' : (p : ResidueField R) = 0 := natCast_eq_zero_of_algebra h _
  obtain ⟨-, -, -, k₁, k₂, k₃, -⟩ := T.dieudonne_ranks_field_char_p hW p _ h' (G.baseChange (ResidueField R))
  have bN := liftSemi_rig_bijective (ResidueField R) G h (Or.inr (@Module.Projective.of_free _ _ _ _ _ f₁))
  have bM := liftSemi_frobTwist_rig_bijective h G (ResidueField R) h'
    (@Module.Projective.of_free _ _ _ _ _ g₁)
  have e₁ := range_rigExtMap_verschiebung_le h G
  have e₂ := LinearMap.range_le_ker_iff.2 (rigExtMap_relFrob_comp_rigOfOmega h G)
  have e₃ := ker_relFrob_le_of_residueField h G h' bN bM g₃ f₂ (k₂.trans k₁.symm).le
  have e₄ := range_relFrob_eq_span h G _ ((T.frobenius_pullback_basis hW p R h G).1 _ (Module.finBasis R G.RigExt)).2
  have e₅ : LinearMap.range (rigExtMap (relFrob h G)) ≤
      LinearMap.ker (rigExtMap (verschiebung h G)) := by
    refine e₄.le.trans (Submodule.span_le.2 ?_)
    rintro _ ⟨x, rfl⟩
    exact rigExtMap_verschiebung_absFrob_rig h G x
  have e₆ := ker_verschiebung_le_of_residueField h G h' bN bM f₃ g₂
    (fun z => LinearMap.mem_ker.1 (e₅ (LinearMap.mem_range_self _ z))) k₃.le
  exact ⟨le_antisymm e₁ (le_trans e₂ e₃), le_antisymm (le_trans e₃ e₁) e₂, le_antisymm e₆ e₅, e₄⟩

end PDivGroup

end GlobalTheory
