import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem dc_common {G : Type} [Group G] (K K' : Subgroup G) (x : G) :
    ∃ s : Finset (MulAction.orbit K (x : G ⧸ K')), ∀ (M : Type) [AddCommGroup M] [Module ℂ M]
      (ρ : Representation ℂ G M) (v : M), Hi.dc ρ K K' x v = ∑ q ∈ s, ρ (q : G ⧸ K').out v := by
  by_cases h : Finite (MulAction.orbit K (x : G ⧸ K'))
  · letI := Fintype.ofFinite (MulAction.orbit K (x : G ⧸ K'))
    refine ⟨Finset.univ, fun M _ _ ρ v => ?_⟩
    rw [Hi.dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply]
  · refine ⟨∅, fun M _ _ ρ v => ?_⟩
    rcases subsingleton_or_nontrivial M with hM | hM
    · exact Subsingleton.elim _ _
    have hs : (Function.support fun q : MulAction.orbit K (x : G ⧸ K') => ρ (q : G ⧸ K').out) = Set.univ := by
      refine Set.eq_univ_of_forall fun q hq => ?_
      have h1 : ρ ((q : G ⧸ K').out⁻¹ * (q : G ⧸ K').out) = 0 := by rw [map_mul, show ρ (q : G ⧸ K').out = 0 from hq, mul_zero]
      rw [inv_mul_cancel, map_one] at h1
      exact one_ne_zero h1
    rw [Hi.dc, finsum_of_infinite_support, Finset.sum_empty, LinearMap.zero_apply]
    rw [hs]
    exact fun hf => h (Set.finite_univ_iff.1 hf)

private theorem killed_of_mem_iSup {G V U ι J : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G U) (hσ : σ.IsIrreducible) (f : ι → U →ₗ[ℂ] V)
    (hf : ∀ i g u, f i (σ g u) = ρ g (f i u)) (T : J → V →ₗ[ℂ] V) (S : J → U →ₗ[ℂ] U)
    (hTS : ∀ j i u, f i (S j u) = T j (f i u))
    (hT : ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → ∀ j, ∀ x ∈ W, T j x ∈ W)
    (φ : V) (h0 : φ ≠ 0) (hK : ∀ j, T j φ = 0)
    (hφ : φ ∈ ⨆ i, LinearMap.range (f i)) : ∃ v : U, v ≠ 0 ∧ ∀ j, S j v = 0 := by
  classical
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hφ
  have key : ∀ s : Finset ι, ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → φ ∉ W →
      φ ∈ W ⊔ ⨆ i ∈ s, LinearMap.range (f i) → ∃ v : U, v ≠ 0 ∧ ∀ j, S j v = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro W _ h1 h2; exact absurd (by simpa using h2) h1
    | insert i s _ ih =>
      intro W hW h1 h2
      rw [Finset.iSup_insert, ← sup_assoc] at h2
      by_cases h3 : φ ∈ W ⊔ LinearMap.range (f i)
      · obtain ⟨x, hx, _, ⟨v, rfl⟩, e⟩ := Submodule.mem_sup.1 h3
        have hv : f i v ∉ W := fun h => h1 (e ▸ add_mem hx h)
        have hc : W.comap (f i) = ⊥ := by
          refine (((GlobalTheory.CuspRep.isIrreducible_iff σ).1 hσ).2 _ fun g u hu => ?_).resolve_right fun h => hv ?_
          · rw [Submodule.mem_comap, hf]; exact hW g _ hu
          · have : v ∈ W.comap (f i) := h ▸ Submodule.mem_top
            exact this
        refine ⟨v, fun h => hv (by rw [h, map_zero]; exact zero_mem _), fun j => ?_⟩
        have h4 : S j v ∈ W.comap (f i) := by
          have h5 := hK j
          rw [← e, map_add] at h5
          rw [Submodule.mem_comap, hTS, eq_neg_of_add_eq_zero_right h5]
          exact neg_mem (hT W hW j x hx)
        rwa [hc, Submodule.mem_bot] at h4
      · refine ih _ (fun g y hy => ?_) h3 h2
        obtain ⟨x, hx, _, ⟨v, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hy
        rw [map_add, ← hf]
        exact Submodule.add_mem_sup (hW g x hx) ⟨_, rfl⟩
  exact key s ⊥ (fun g x hx => by simp_all) (by simpa using h0) (by simpa using hs)

private theorem dc_eigen_descend {G V U ι : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G U) (hσ : σ.IsIrreducible) (f : ι → U →ₗ[ℂ] V)
    (hf : ∀ i g u, f i (σ g u) = ρ g (f i u)) (K : Subgroup G) (x : G) (lam : ℂ)
    (φ : V) (h0 : φ ≠ 0) (hK : φ ∈ Hi.fixd ρ K) (hl : Hi.dc ρ K K x φ = lam • φ)
    (hφ : φ ∈ ⨆ i, LinearMap.range (f i)) :
    ∃ v : U, v ≠ 0 ∧ v ∈ Hi.fixd σ K ∧ Hi.dc σ K K x v = lam • v := by
  obtain ⟨s, hs⟩ := dc_common K K x
  obtain ⟨v, hv0, hv⟩ := killed_of_mem_iSup ρ σ hσ f hf
    (fun j : Option K => j.elim (Hi.dc ρ K K x - lam • LinearMap.id) fun k => ρ k - LinearMap.id)
    (fun j : Option K => j.elim (Hi.dc σ K K x - lam • LinearMap.id) fun k => σ k - LinearMap.id)
    (by
      rintro (_ | k) i u
      · simp only [Option.elim, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul, hs,
          map_sum, hf]
      · simp only [Option.elim, LinearMap.sub_apply, LinearMap.id_apply, map_sub, hf])
    (by
      rintro W hW (_ | k) y hy
      · simp only [Option.elim, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hs]
        exact sub_mem (Submodule.sum_mem _ fun q _ => hW _ _ hy) (W.smul_mem _ hy)
      · simp only [Option.elim, LinearMap.sub_apply, LinearMap.id_apply]
        exact sub_mem (hW _ _ hy) hy)
    φ h0
    (by
      rintro (_ | k)
      · simp only [Option.elim, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hl, sub_self]
      · simp only [Option.elim, LinearMap.sub_apply, LinearMap.id_apply]
        exact sub_eq_zero.2 (hK k k.2))
    hφ
  exact ⟨v, hv0, fun k hk => sub_eq_zero.1 (hv (some ⟨k, hk⟩)), sub_eq_zero.1 (hv none)⟩

theorem UpperTheory.hasUEigenvalue_of_locIsotypic :
    ∀ (F : Type) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) (Af F)) V) (σ : SmIrr (GL (Fin 2) (w.adicCompletion F))), LocIsotypic ρ w σ → ∀ (c : ℕ) (lam : ℂ), HasU w (ρ.comp (locGL F 2 w)) c lam → HasU w σ.ρ c lam := by
  intro F _ _ w V _ _ ρ σ ⟨_, htop⟩ c lam ⟨φ, h0, hK, hl⟩
  exact dc_eigen_descend (ρ.comp (locGL F 2 w)) σ.ρ σ.irred
    (fun f : {f : σ.V →ₗ[ℂ] V // ∀ g v, f (σ.ρ g v) = ρ (locGL F 2 w g) (f v)} => f.1) (fun f => f.2)
    (K1 w c) _ lam φ h0 hK hl (htop ▸ Submodule.mem_top)
