import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.HeckeActMem
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Heckebasic
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EvalFg

open Formalism.UG Formalism.UG.P

noncomputable section

namespace CompanionTheory.HeckeA

variable {G H W : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] (ι : H →* G) (K : Subgroup H)

def op (φ : H → ℂ) (f : G → W) (g : G) : W := ∑ᶠ c : H ⧸ K, φ c.out • f (g * ι c.out)

def Inv (f : G → W) : Prop := ∀ g, ∀ k ∈ K, f (g * ι k) = f g

open Classical in
theorem coset_sum_eq (J : Subgroup G) (hJ : ∀ h, ι h ∈ J ↔ h ∈ K) (d : H) {f : G → W} (hf : Inv ι K f) (g : G)
    {D : Set G} (hD : ∀ x, x ∈ D ↔ ∃ h ∈ DoubleCoset.doubleCoset d (K : Set H) K, ι h = x) :
    (∑ᶠ c : G ⧸ J, if hc : ∃ x ∈ D, (x : G ⧸ J) = c then f (g * hc.choose) else 0) = op ι K (dosetInd ℂ K d) f g := by
  have hmul : ∀ h ∈ DoubleCoset.doubleCoset d (K : Set H) K, ∀ k ∈ K,
      h * k ∈ DoubleCoset.doubleCoset d (K : Set H) K := fun h hh k hk => by
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hh
    exact DoubleCoset.mem_doubleCoset.2 ⟨a, ha, b * k, K.mul_mem hb hk, by group⟩
  have heq : ∀ h h' : H, ((ι h : G) : G ⧸ J) = (ι h' : G) ↔ h⁻¹ * h' ∈ K := fun h h' => by
    rw [QuotientGroup.eq, ← map_inv, ← map_mul, hJ]
  have hinj : Function.Injective fun c : H ⧸ K => ((ι c.out : G) : G ⧸ J) := fun c c' h => by
    rw [← c.out_eq', ← c'.out_eq']
    exact QuotientGroup.eq.2 ((heq _ _).1 h)
  rw [← finsum_mem_univ, finsum_mem_inter_support_eq _ _ (Set.range fun c : H ⧸ K => ((ι c.out : G) : G ⧸ J)),
    finsum_mem_range hinj]
  · refine finsum_congr fun c => ?_
    split_ifs with hc
    · obtain ⟨h, hh, e⟩ := (hD _).1 hc.choose_spec.1
      have e2 := hc.choose_spec.2
      rw [← e] at e2 ⊢
      have hk := (heq _ _).1 e2
      have e3 : c.out = h * (h⁻¹ * c.out) := by group
      rw [dosetInd, Set.indicator_of_mem (e3 ▸ hmul h hh _ hk), Pi.one_apply, one_smul, e3, map_mul, ← mul_assoc,
        hf _ _ hk]
    · rw [dosetInd, Set.indicator_of_notMem fun h => hc ⟨_, (hD _).2 ⟨_, h, rfl⟩, rfl⟩, zero_smul]
  · ext c
    simp only [Set.mem_inter_iff, Set.mem_univ, true_and, iff_and_self, Function.mem_support]
    intro hc
    obtain ⟨x, hx, rfl⟩ : ∃ x ∈ D, (x : G ⧸ J) = c := by
      by_contra h
      exact hc (dif_neg h)
    obtain ⟨h, -, rfl⟩ := (hD _).1 hx
    exact ⟨(h : H ⧸ K), (heq _ _).2 (QuotientGroup.eq.1 (QuotientGroup.out_eq' _))⟩

variable {K}

theorem exists_sum (hK : IsCommensurated K) {φ : H → ℂ} (hφ : φ ∈ Hecke ℂ K) :
    ∃ S : Finset (H ⧸ K), ∀ (f : G → W) (g : G), op ι K φ f g = ∑ c ∈ S, φ c.out • f (g * ι c.out) :=
  ⟨(finite_supp K hK φ hφ).toFinset, fun f g => finsum_eq_sum_of_support_subset _ fun c hc => by
    rw [Set.Finite.coe_toFinset]
    exact fun h => hc (by simp only [h, zero_smul])⟩

theorem op_comm_same (hK : IsCommensurated K) {φ ψ : H → ℂ} (hφ : φ ∈ Hecke ℂ K) (hψ : ψ ∈ Hecke ℂ K)
    (hc : conv K φ ψ = conv K ψ φ) {f : G → W} (hf : Inv ι K f) : op ι K φ (op ι K ψ f) = op ι K ψ (op ι K φ f) := by
  funext g
  have hm : (fun h => f (g * ι h)) ∈ AMF ℂ (⊥ : Subgroup H) K (1 : Representation ℂ (⊥ : Subgroup H) W) := by
    rintro ⟨γ, hγ⟩ h κ
    rw [Subgroup.mem_bot] at hγ
    subst hγ
    show f (g * ι (1 * h * κ)) = f (g * ι h)
    rw [one_mul, map_mul, ← mul_assoc, hf _ _ κ.2]
  have key : ∀ a b : H → ℂ, op ι K a (op ι K b f) g = hAct K a (hAct K b fun h => f (g * ι h)) 1 := fun a b => by
    simp only [op, hAct, one_mul, map_mul, mul_assoc]
  rw [key, key, ← hecke_act_mul H ⊥ K ℂ W 1 hK φ hφ ψ hψ _ hm, ← hecke_act_mul H ⊥ K ℂ W 1 hK ψ hψ φ hφ _ hm, hc]

theorem op_conj {φ : H → ℂ} (hφ : IsBiInv K φ) {f : G → W} (hf : Inv ι K f) {κ : G} {u : H} (hu : u ∈ K) {c : ℂ}
    (hκ : ∀ h, κ * ι h * κ⁻¹ = ι (u * h * u⁻¹)) (hc : ∀ g, f (g * κ) = c • f g) (hfin : IsCommensurated K)
    (hφ' : φ ∈ Hecke ℂ K) (g : G) : op ι K φ f (g * κ) = c • op ι K φ f g := by
  have h1 : op ι K φ f g = ∑ᶠ z : H ⧸ K, φ z.out • f (g * ι (u * z.out)) := by
    rw [op, ← finsum_out_mul K u (fun h => φ h • f (g * ι h)) fun h k => by
      rw [map_mul, ← mul_assoc, hf _ _ k.2, show φ (h * k) = φ h by simpa using hφ 1 k h]]
    exact finsum_congr fun z => by rw [show φ (u * z.out) = φ z.out by simpa using hφ ⟨u, hu⟩ 1 z.out]
  rw [h1, smul_finsum' c ((finite_supp K hfin φ hφ').subset fun z hz h => hz (by simp only [h, zero_smul])), op]
  refine finsum_congr fun z => ?_
  rw [smul_comm, show g * κ * ι z.out = g * (κ * ι z.out * κ⁻¹) * κ by group, hc, hκ, map_mul ι _ u⁻¹, ← mul_assoc,
    hf _ _ (K.inv_mem hu)]

section FG

variable {R : Type} [CommRing R] [Algebra R ℂ]

theorem eval_fg {σ : Type} {M₀ : Submodule R ℂ} (h₀ : M₀.FG) (P : MvPolynomial σ ℂ) :
    ∃ M : Submodule R ℂ, M.FG ∧ ∀ v : σ → ℂ, (∀ i, v i ∈ M₀) → MvPolynomial.eval v P ∈ M :=
  _root_.UpperTheory.Reformulated.B.Qn15.eval_fg h₀ P

theorem apply_fg [Module R W] [IsScalarTower R ℂ W] {σ κ : Type} [Fintype κ] [DecidableEq κ] (b : Module.Basis κ ℂ W)
    (P : κ → κ → MvPolynomial σ ℂ) {M₀ : Submodule R ℂ} (h₀ : M₀.FG) (w : W) :
    ∃ N : Submodule R W, N.FG ∧ ∀ (A : W →ₗ[ℂ] W) (v : σ → ℂ), (∀ i, v i ∈ M₀) →
      (LinearMap.toMatrix b b A = fun i j => MvPolynomial.eval v (P i j)) → A w ∈ N := by
  choose M h1 h2 using fun p : κ × κ => eval_fg h₀ (P p.1 p.2)
  refine ⟨⨆ p : κ × κ, (M p).map ((LinearMap.toSpanSingleton ℂ W (b.repr w p.2 • b p.1)).restrictScalars R),
    Submodule.fg_iSup _ fun p => (h1 p).map _, fun A v hv hA => ?_⟩
  rw [← b.sum_repr (A w)]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [show b.repr (A w) i = ∑ j, LinearMap.toMatrix b b A i j * b.repr w j from
    (congrFun (LinearMap.toMatrix_mulVec_repr b b A w) i).symm, Finset.sum_smul]
  refine Submodule.sum_mem _ fun j _ => Submodule.mem_iSup_of_mem (i, j) ⟨_, h2 (i, j) v hv, ?_⟩
  rw [hA, mul_smul]
  rfl

end FG

end CompanionTheory.HeckeA
