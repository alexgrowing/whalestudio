import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Formalism.LocalToGlobal.Columns.PolyFnLemmas

noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms

section General

variable {K : Type} [Field K] (σ : K →+* ℂ) {V W C J : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]

theorem li_pi_of_basis [Finite C] [Fintype J] (e : Module.Basis J K V) (ev : V →ₛₗ[σ] W)
    (he : LinearIndependent ℂ fun j => ev (e j)) {κ : Type} (b : κ → C → V) (hb : LinearIndependent K b) :
    LinearIndependent ℂ fun i => fun c => ev (b i c) := by
  classical
  letI : Algebra K ℂ := σ.toAlgebra
  let r : (C → V) →ₗ[K] (C × J → K) :=
    LinearMap.pi fun p => (e.coord p.2) ∘ₗ LinearMap.proj p.1
  have hr : LinearMap.ker r = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro f hf
    funext c
    apply e.ext_elem
    intro j
    simpa [r] using congrFun hf (c, j)
  have h1 := (linearIndependent_algebraMap_comp_iff (S := ℂ)).2 (hb.map' r hr)
  let T : (C × J → ℂ) →ₗ[ℂ] (C → W) :=
    LinearMap.pi fun c => ∑ j, (LinearMap.proj (c, j) : (C × J → ℂ) →ₗ[ℂ] ℂ).smulRight (ev (e j))
  have hT : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro u hu
    funext p
    have h2 : ∑ j, u (p.1, j) • ev (e j) = 0 := by
      simpa [T, LinearMap.sum_apply] using congrFun hu p.1
    exact Fintype.linearIndependent_iff.1 he (fun j => u (p.1, j)) h2 p.2
  have h3 := h1.map' T hT
  suffices hs : (fun i => fun c => ev (b i c)) = T ∘ fun i => algebraMap K ℂ ∘ (r ∘ b) i by
    rw [hs]
    exact h3
  funext i c
  have h4 : b i c = ∑ j, e.repr (b i c) j • e j := (e.sum_repr _).symm
  conv_lhs => rw [h4]
  simp only [map_sum, LinearMap.map_smulₛₗ]
  simp [T, r, LinearMap.sum_apply, RingHom.algebraMap_toAlgebra]

theorem mem_span_basis_image [Fintype J] (e : Module.Basis J K V) (ev : V →ₛₗ[σ] W) (x : V) :
    ev x ∈ Submodule.span ℂ (Set.range fun j => ev (e j)) := by
  rw [← e.sum_repr x, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [LinearMap.map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem rho_sum_translates {G : Type} [Group G] [Fintype G] (ρ : G →* Module.End K V) (g : G) (x : V) :
    ρ g (∑ t, ρ t x) = ∑ t, ρ t x := by
  rw [map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun t => ?_
  simp [map_mul]

end General

namespace GStep

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n)

omit [StarRing E] [StarRing K] in

theorem evV_rho_eq_tr (b : S.β) (g : S.G b) (F : VV K lam) :
    evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (S.rho emb lam b g F) =
      S.tr emb σ b g (evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ F) := by
  funext y
  have h1 : S.rho emb lam b g F = ((S.chr b g : Kˣ) : K) • rhoVr emb lam (S.gam b g) F := rfl
  rw [h1, LinearMap.map_smulₛₗ, tr, trFr_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  refine evV_rhoVr_tr emb _ lam σ _ F y _ ?_
  have h2 : y = frMul emb σ (S.gam b g) (frMul emb σ (S.gam b g)⁻¹ y) := by
    rw [← frMul_mul, mul_inv_cancel, frMul_one]
  intro τ
  exact congrFun (congrArg Subtype.val h2) τ

theorem lawBasis_of_ok (h : (S.fam emb lam).Ok) : S.LawBasis emb σ lam h := by
  classical
  haveI : Fintype S.Cl := h.fintypeCl
  constructor
  · have h1 : LinearIndependent K fun a => ((S.csd emb lam h).basis a).1 :=
      (S.csd emb lam h).basis.linearIndependent.map' (S.csd emb lam h).Forms.subtype (Submodule.ker_subtype _)
    exact li_pi_of_basis σ (C := S.Cl) (S.csd emb lam h).bV (evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ)
      (evV_linearIndependent emb _ lam σ (fr0 emb σ n) _ (S.csd emb lam h).bV.linearIndependent) _ h1
  · refine le_antisymm ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩ c
      refine ⟨evV_mem_ValC emb _ lam σ _, fun g => ?_⟩
      have h1 := ((S.csd emb lam h).basis a).2 c g
      have h2 := S.evV_rho_eq_tr emb σ lam c.1 g.1 (((S.csd emb lam h).basis a).1 c)
      exact h2.symm.trans (congrArg (evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ) h1)
    · intro φ hφ
      rw [← Finset.univ_sum_single φ]
      refine Submodule.sum_mem _ fun c _ => ?_
      letI : Fintype (S.Stab c) := (S.csd emb lam h).finGam c
      let A : (Fr emb σ n → ℂ) →ₗ[ℂ] (S.Cl → Fr emb σ n → ℂ) :=
        LinearMap.single ℂ (fun _ : S.Cl => Fr emb σ n → ℂ) c ∘ₗ ∑ g : S.Stab c, (S.tr emb σ c.1 g.1).toLinearMap
      have hA : ∀ w, A w = Pi.single c (∑ g : S.Stab c, S.tr emb σ c.1 g.1 w) := fun w => by
        simp [A, LinearMap.sum_apply]
      have hle : ValC (Gr emb σ n) lam ≤ (Submodule.span ℂ
          (Set.range fun a => S.embF emb σ lam h ((S.hlat emb lam h).b a))).comap A := by
        rw [← span_evV, Submodule.span_le]
        rintro _ ⟨F, rfl⟩
        let ρc : S.Stab c →* Module.End K (VV K lam) :=
          (S.rho emb lam c.1).comp (MulAction.stabilizer (S.G c.1) (S.rep c)).subtype
        let x : S.FormsK emb lam h := ⟨(Pi.single c (∑ t, ρc t F) : S.Cl → VV K lam), by
          intro c' γ
          by_cases hc : c' = c
          · subst hc
            show ρc γ ((Pi.single c' (∑ t, ρc t F) : S.Cl → VV K lam) c') =
              (Pi.single c' (∑ t, ρc t F) : S.Cl → VV K lam) c'
            rw [Pi.single_eq_same]
            exact rho_sum_translates ρc γ F
          · show S.rho emb lam c'.1 γ.1 ((Pi.single c (∑ t, ρc t F) : S.Cl → VV K lam) c') =
              (Pi.single c (∑ t, ρc t F) : S.Cl → VV K lam) c'
            rw [Pi.single_eq_of_ne hc, map_zero]⟩
        have hx : A (evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ F) = S.embF emb σ lam h x := by
          rw [hA]
          funext c'
          show _ = evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ ((Pi.single c (∑ t, ρc t F) : S.Cl → VV K lam) c')
          by_cases hc : c' = c
          · subst hc
            rw [Pi.single_eq_same, Pi.single_eq_same, map_sum]
            exact Finset.sum_congr rfl fun g _ => (S.evV_rho_eq_tr emb σ lam c'.1 g.1 F).symm
          · rw [Pi.single_eq_of_ne hc, Pi.single_eq_of_ne hc, map_zero]
        rw [SetLike.mem_coe, Submodule.mem_comap, hx]
        exact mem_span_basis_image σ (S.hlat emb lam h).b (S.embF emb σ lam h) x
      have h1 := Submodule.mem_comap.1 (hle (hφ c).1)
      have h2 : A (φ c) = (Fintype.card (S.Stab c) : ℂ) • (Pi.single c (φ c) : S.Cl → Fr emb σ n → ℂ) := by
        rw [hA, Finset.sum_congr rfl fun g _ => (hφ c).2 g, Finset.sum_const, Finset.card_univ, ← Pi.single_smul',
          Nat.cast_smul_eq_nsmul]
      rw [h2] at h1
      exact (Submodule.smul_mem_iff _ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)).1 h1

end GStep

theorem lawBasis_all : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι]
    {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n),
    FOk emb σ → S.Ok → ∀ h, S.LawBasis emb σ lam h :=
  fun S emb σ lam _ _ h => S.lawBasis_of_ok emb σ lam h

end GlobalTheory.Mem.Col2
