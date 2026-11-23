import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPrechartPointsSeparateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrechartTranslateOrderStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFiniteSemiabelianOverAlgClosedStatement
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.OrdLocProd

theorem exists_isLocalizedModule_pi {R K C T : Type} [CommRing R] [CommRing K] [Algebra R K] [CommRing C] [Algebra R C]
    [CommGroup T] [Finite T] (r : R) (hr : IsUnit (algebraMap R C r)) (t : (C →ₐ[R] K) → T) (H : Subgroup T)
    (hH : ∀ x, x ∈ H ↔ ∃ ψ, t ψ = x) (O : Subalgebra R (T → K))
    (hsep : ∀ a : C, (∀ ψ : C →ₐ[R] K, ψ a = 0) → a = 0)
    (hres : ∀ f ∈ O, ∀ s : T, ∃ a : C, ∀ ψ : C →ₐ[R] K, ψ a = f (s * t ψ))
    (hext : ∀ (s : T) (u : C), ∃ (k : ℕ) (g : T → K), g ∈ O ∧ (∀ ψ : C →ₐ[R] K, g (s * t ψ) = algebraMap R K r ^ k * ψ u) ∧
      ∀ x, (∀ ψ : C →ₐ[R] K, x ≠ s * t ψ) → g x = 0) :
    ∃ ϕ : O →ₗ[R] (T ⧸ H → C), IsLocalizedModule (Submonoid.powers r) ϕ := by
  classical
  have hext' : ∀ a b : C, (∀ ψ : C →ₐ[R] K, ψ a = ψ b) → a = b := fun a b h => by
    rw [← sub_eq_zero]
    exact hsep _ fun ψ => by rw [map_sub, h, sub_self]
  choose φ hφ using hres
  let ϕ : O →ₗ[R] (T ⧸ H → C) :=
    { toFun := fun f s => φ f.1 f.2 s.out
      map_add' := fun f g => funext fun s => hext' _ _ fun ψ => by
        rw [Pi.add_apply, map_add, hφ, hφ, hφ]; rfl
      map_smul' := fun a f => funext fun s => hext' _ _ fun ψ => by
        rw [Pi.smul_apply, map_smul, hφ, hφ]; rfl }
  have hϕ : ∀ (f : O) (s : T ⧸ H) (ψ : C →ₐ[R] K), ψ (ϕ f s) = f.1 (s.out * t ψ) := fun f s ψ => hφ _ _ _ _
  refine ⟨ϕ, ?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    obtain ⟨v, hv⟩ := hr.pow n
    rw [Module.End.isUnit_iff]
    have hv' : ∀ x : T ⧸ H → C, algebraMap R (Module.End R (T ⧸ H → C)) (r ^ n) x = (v : C) • x := fun x => by
      rw [hv, ← map_pow, algebraMap_smul, Module.algebraMap_end_apply]
    constructor
    · intro x y h
      have h' : (v : C) • x = (v : C) • y := by rw [← hv', ← hv']; exact h
      have := congrArg (fun z => ((v⁻¹ : Cˣ) : C) • z) h'
      simpa [smul_smul] using this
    · intro y
      refine ⟨((v⁻¹ : Cˣ) : C) • y, ?_⟩
      show algebraMap R (Module.End R (T ⧸ H → C)) (r ^ n) _ = _
      rw [hv', smul_smul, Units.mul_inv, one_smul]
  · intro u
    letI : Fintype (T ⧸ H) := Fintype.ofFinite _
    choose k g hgO hg1 hg0 using fun s : T ⧸ H => hext s.out (u s)
    let M : ℕ := Finset.univ.sup k
    have hM : ∀ s, k s ≤ M := fun s => Finset.le_sup (f := k) (Finset.mem_univ s)
    refine ⟨(∑ s, r ^ (M - k s) • (⟨g s, hgO s⟩ : O), ⟨r ^ M, M, rfl⟩), ?_⟩
    funext s
    apply hext'
    intro ψ
    show ψ (r ^ M • u s) = _
    rw [map_sum, Finset.sum_apply, map_sum, Finset.sum_eq_single s]
    · rw [map_smul, map_smul, Pi.smul_apply, map_smul, hϕ]
      show _ = r ^ (M - k s) • g s _
      rw [hg1, ← map_pow, ← Algebra.smul_def, smul_smul, ← pow_add, Nat.sub_add_cancel (hM s)]
    · intro s' _ hs'
      rw [map_smul, Pi.smul_apply, map_smul, hϕ]
      show r ^ (M - k s') • g s' _ = 0
      rw [hg0, smul_zero]
      intro ψ' h
      apply hs'
      have h1 : ∀ (a : T ⧸ H) (χ : C →ₐ[R] K), ((a.out * t χ : T) : T ⧸ H) = a := fun a χ => by
        rw [QuotientGroup.mk_mul_of_mem _ ((hH _).2 ⟨χ, rfl⟩), QuotientGroup.out_eq']
      rw [← h1 s' ψ', ← h, h1]
    · intro h
      exact absurd (Finset.mem_univ s) h
  · intro f g h
    refine ⟨1, ?_⟩
    congr 1
    apply Subtype.ext
    funext x
    obtain ⟨y, hy⟩ := QuotientGroup.mk_out_eq_mul H x
    obtain ⟨ψ, hψ⟩ := (hH _).1 (H.inv_mem y.2)
    have hx : x = (x : T ⧸ H).out * t ψ := by rw [hy, hψ, mul_inv_cancel_right]
    rw [hx, ← hϕ, ← hϕ, h]

theorem ord_isLocalizedModule : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : ℕ), N ≠ 0 → ∀ (q : PrimeSpectrum R) (c : PreChart G N q), c.IsGrp → ∃ (F : Type) (_ : AddCommGroup F) (_ : Module R F) (_ : Module (Localization.Away c.r) F) (_ : IsScalarTower R (Localization.Away c.r) F) (_ : Module.Finite (Localization.Away c.r) F) (_ : Module.Free (Localization.Away c.r) F) (ϕ : ord G N K →ₗ[R] F), IsLocalizedModule (Submonoid.powers c.r) ϕ := by
  intro R K _ _ _ _ _ _ _ _ G _ _ hG N hN q c hc
  have hsep := (GlobalTheory.T.torsion_prechart_points_separate R K G hG N hN q c).2
  have hext := GlobalTheory.T.prechart_translate_order R K G hG N hN q c hc
  haveI : Finite (Tors G N K) := GlobalTheory.T.torsion_finite_semiabelian_over_alg_closed R K G hG N hN
  have hr0 : c.r ≠ 0 := fun h => c.hr (h ▸ q.asIdeal.zero_mem)
  have hrK : IsUnit (algebraMap R K c.r) :=
    isUnit_iff_ne_zero.2 fun h => hr0 (IsFractionRing.injective R K (by rw [h, map_zero]))
  have hr : IsUnit (algebraMap R c.C c.r) := by
    rw [IsScalarTower.algebraMap_apply R (Localization.Away c.r) c.C]
    exact (IsLocalization.Away.algebraMap_isUnit c.r).map _
  let H₀ : Submonoid (Tors G N K) :=
    { carrier := {x | ∃ ψ : c.C →ₐ[R] K, torsMap ψ c.j = x}
      mul_mem' := by
        rintro _ _ ⟨ψ, rfl⟩ ⟨ψ', rfl⟩
        exact hc.2 K ψ ψ'
      one_mem' := by
        obtain ⟨ψ, hψ⟩ := hc.1
        let l : Localization.Away c.r →ₐ[R] K :=
          { IsLocalization.Away.lift c.r hrK with commutes' := IsLocalization.Away.lift_eq c.r hrK }
        refine ⟨l.comp ψ, Subtype.ext ?_⟩
        have h1 : spOver ψ ≫ c.j.1 = 1 := congrArg Subtype.val hψ
        rw [torsMap_val, ← spOver_comp, Category.assoc, h1, tors_one_val, MonObj.comp_one] }
  let H : Subgroup (Tors G N K) :=
    { H₀ with
      inv_mem' := fun {x} hx => by
        have h1 : x⁻¹ = x ^ (orderOf x - 1) := by
          have hp : 0 < orderOf x := orderOf_pos x
          rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel hp, pow_orderOf_eq_one]
        show x⁻¹ ∈ H₀
        rw [h1]
        exact H₀.pow_mem hx _ }
  obtain ⟨ϕ, hϕ⟩ := exists_isLocalizedModule_pi c.r hr (fun ψ : c.C →ₐ[R] K => torsMap ψ c.j) H (fun _ => Iff.rfl)
    (ord G N K) hsep (fun f hf s => by
      obtain ⟨σ, hσ, hσf⟩ := hf s
      exact ⟨σ c.C c.j, fun ψ => by rw [← hσ, hσf]⟩) hext
  exact ⟨Tors G N K ⧸ H → c.C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ϕ, hϕ⟩

end GlobalTheory.OrdLocProd
