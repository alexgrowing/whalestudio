import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLieBasisCoeffsOfDerivationAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantFieldCoefficientsOfLinearVectorFi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieBasisDualPointsOfTangentModuleBasis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.TangentOrigin

noncomputable section

namespace GlobalTheory.GcDual

def cHom {K : Type} [Field K] {X : Scheme.{0}} (p : X ⟶ Sp K) (W : X.Opens) : K →+* Γ(X, W) :=
  (p.appLE ⊤ W (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

theorem coeffs_zero {K : Type} [Field K] (P₀ : Out.PolAV (Sp K)) (n : ℕ)
    (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left)
    (hd : ∀ a, IsInv P₀.A (v a) (dd a)) (W : P₀.A.left.Opens) (hW : IsAffineOpen W)
    {C : Type} [CommRing C] (ψ : Γ(P₀.A.left, W) →+* C) (c : Fin n → C)
    (hc : ∀ f, ∑ a, c a * ψ (dd a W f) = 0) : c = 0 := by
  haveI := P₀.smoothDim
  haveI : Smooth P₀.A.hom := SmoothOfRelativeDimension.smooth P₀.g _
  letI : Algebra K C := (ψ.comp (cHom P₀.A.hom W)).toAlgebra
  obtain ⟨x, hx, ex⟩ := exists_evalPt_eq hW ψ
  have hxp : x ≫ P₀.A.hom = (ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := K) C).hom := by
    refine (eq_spMap_of_evalPt _ (algebraMap K C) fun a => ?_).trans rfl
    rw [← evalPt_constFn P₀.A.hom x W hx, ex]
    rfl
  let y : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := K) C ⟶ P₀.A := Over.homMk x hxp
  obtain ⟨c₀, -, hu⟩ := GlobalTheory.VertCoeffRing.existsUnique_coeff_alg (GlobalTheory.VertCoeffRing.isLieBasis_tvE v)
    (fun B _ _ e he z O h => GlobalTheory.VertCoeffRing.evalPt_lieExp v dd hd B e he z O h) y hW hx (fun _ => 0)
    (fun _ _ => by simp) (fun _ _ => by simp) (fun _ => rfl)
  have h1 := hu c (fun f => by simpa [y, ex] using (hc f).symm)
  have h2 := hu 0 (fun f => by simp)
  rw [h1, h2]

end GlobalTheory.GcDual

namespace GlobalTheory.GcDual

variable {A : Type} [CommRing A] {n : ℕ}

theorem mem_smul_top_of_forall_mem (I : Ideal A) (x : Fin n → A) (hx : ∀ b, x b ∈ I) :
    x ∈ I • (⊤ : Submodule A (Fin n → A)) := by
  rw [← Finset.univ_sum_single x]
  refine Submodule.sum_mem _ fun b _ => ?_
  have : Pi.single b (x b) = x b • (Pi.single b 1 : Fin n → A) := by
    rw [← Pi.single_smul, smul_eq_mul, _root_.mul_one]
  rw [this]
  exact Submodule.smul_mem_smul (hx b) trivial

theorem eq_top_of_forall_maximal (M : Submodule A (Fin n → A))
    (h : ∀ m : Ideal A, m.IsMaximal → ∀ x, x ∈ M ⊔ m • (⊤ : Submodule A (Fin n → A))) : M = ⊤ := by
  have hQ : ∀ m : Ideal A, m.IsMaximal → ∃ r : A, r - 1 ∈ m ∧ ∀ q : (Fin n → A) ⧸ M, r • q = 0 := by
    intro m hm
    have hle : (⊤ : Submodule A ((Fin n → A) ⧸ M)) ≤ m • ⊤ := by
      intro q _
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective M q
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (h m hm x)
      have hz' : M.mkQ z ∈ m • (⊤ : Submodule A ((Fin n → A) ⧸ M)) := by
        have : m • (⊤ : Submodule A (Fin n → A)) ≤ (m • (⊤ : Submodule A ((Fin n → A) ⧸ M))).comap M.mkQ :=
          Submodule.smul_le.2 fun r hr t _ => by
            rw [Submodule.mem_comap, map_smul]
            exact Submodule.smul_mem_smul hr trivial
        exact this hz
      have e : Submodule.Quotient.mk (p := M) (y + z) = M.mkQ z := by
        rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero M).2 hy, zero_add]; rfl
      rw [e]; exact hz'
    obtain ⟨r, hr, hr'⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m ⊤
      (Module.Finite.fg_top) hle
    exact ⟨r, hr, fun q => hr' q trivial⟩
  have h1 : ∀ q : (Fin n → A) ⧸ M, q = 0 := by
    by_contra hne
    push_neg at hne
    obtain ⟨q₀, hq₀⟩ := hne
    let I : Ideal A := Module.annihilator A ((Fin n → A) ⧸ M)
    have hI : I ≠ ⊤ := by
      intro hI
      have : (1 : A) ∈ I := hI ▸ Submodule.mem_top
      exact hq₀ (by simpa using Module.mem_annihilator.1 this q₀)
    obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
    obtain ⟨r, hr, hr'⟩ := hQ m hm
    have hrI : r ∈ I := Module.mem_annihilator.2 hr'
    have : (1 : A) ∈ m := by
      have := m.sub_mem (hIm hrI) hr
      simpa using this
    exact hm.ne_top ((Ideal.eq_top_iff_one m).2 this)
  rw [eq_top_iff]
  intro x _
  exact (Submodule.Quotient.mk_eq_zero M).1 (h1 _)

end GlobalTheory.GcDual

namespace GlobalTheory.GcDual

theorem span_eq_top {K : Type} [Field K] (P₀ : Out.PolAV (Sp K)) (n : ℕ)
    (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left)
    (hd : ∀ a, IsInv P₀.A (v a) (dd a)) (W : P₀.A.left.Opens) (hW : IsAffineOpen W) :
    Submodule.span Γ(P₀.A.left, W) (Set.range fun f : Γ(P₀.A.left, W) => fun b => dd b W f) = ⊤ := by
  set M := Submodule.span Γ(P₀.A.left, W) (Set.range fun f : Γ(P₀.A.left, W) => fun b => dd b W f) with hM
  refine eq_top_of_forall_maximal M fun m hm x => ?_
  haveI := hm
  letI : Field (Γ(P₀.A.left, W) ⧸ m) := Ideal.Quotient.field m
  let π : Γ(P₀.A.left, W) →+* Γ(P₀.A.left, W) ⧸ m := Ideal.Quotient.mk m
  let S : Submodule (Γ(P₀.A.left, W) ⧸ m) (Fin n → Γ(P₀.A.left, W) ⧸ m) :=
    Submodule.span _ (Set.range fun f : Γ(P₀.A.left, W) => fun b => π (dd b W f))
  have hS : S = ⊤ := by
    by_contra hS
    obtain ⟨φ, hφ0, hφ⟩ := S.exists_le_ker_of_lt_top (lt_top_iff_ne_top.2 hS)
    classical
    let c : Fin n → Γ(P₀.A.left, W) ⧸ m := fun b => φ fun j => if b = j then 1 else 0
    have hc := coeffs_zero P₀ n v dd hd W hW π c fun f => by
      have := hφ (Submodule.subset_span ⟨f, rfl⟩)
      rw [LinearMap.mem_ker, LinearMap.pi_apply_eq_sum_univ] at this
      simpa [c, smul_eq_mul, mul_comm] using this
    apply hφ0
    refine LinearMap.ext fun z => ?_
    rw [LinearMap.pi_apply_eq_sum_univ]
    have : ∀ i, φ (fun j => if i = j then 1 else 0) = 0 := fun i => congrFun hc i
    simp [this]
  have lift : ∀ y ∈ S, ∃ x₀ ∈ M, (fun b => π (x₀ b)) = y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, rfl⟩ := hy
      exact ⟨fun b => dd b W f, Submodule.subset_span ⟨f, rfl⟩, rfl⟩
    | zero => exact ⟨0, M.zero_mem, by ext; simp⟩
    | add y y' _ _ h h' =>
      obtain ⟨x₀, hx₀, rfl⟩ := h
      obtain ⟨x₁, hx₁, rfl⟩ := h'
      exact ⟨x₀ + x₁, M.add_mem hx₀ hx₁, by ext; simp⟩
    | smul s y _ h =>
      obtain ⟨x₀, hx₀, rfl⟩ := h
      obtain ⟨s', rfl⟩ := Ideal.Quotient.mk_surjective s
      exact ⟨s' • x₀, M.smul_mem s' hx₀, by ext; simp [π]⟩
  obtain ⟨x₀, hx₀, e⟩ := lift (fun b => π (x b)) (hS ▸ Submodule.mem_top)
  have hk : x - x₀ ∈ m • (⊤ : Submodule Γ(P₀.A.left, W) (Fin n → Γ(P₀.A.left, W))) :=
    mem_smul_top_of_forall_mem m _ fun b => by
      rw [Pi.sub_apply, ← Ideal.Quotient.eq]
      exact (congrFun e b).symm
  have : x = x₀ + (x - x₀) := by abel
  rw [this]
  exact Submodule.add_mem_sup hx₀ hk

theorem exists_dual_forms : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ W : P₀.A.left.Opens, IsAffineOpen W → ∀ a : Fin n, ∃ (N : ℕ) (g f : Fin N → Γ(P₀.A.left, W)), ∀ b, ∑ i, g i * dd b W (f i) = if a = b then 1 else 0 := by
  intro K _ _ P₀ n v dd hd W hW a
  have hmem : (Pi.single a 1 : Fin n → Γ(P₀.A.left, W)) ∈
      Submodule.span Γ(P₀.A.left, W) (Set.range fun f : Γ(P₀.A.left, W) => fun b => dd b W f) := by
    rw [span_eq_top P₀ n v dd hd W hW]; exact Submodule.mem_top
  obtain ⟨N, g, u, hu⟩ := Submodule.mem_span_set'.1 hmem
  refine ⟨N, g, fun i => (u i).2.choose, fun b => ?_⟩
  have h := congrFun hu b
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  have e : ∀ i, dd b W ((u i).2.choose) = (u i : Fin n → Γ(P₀.A.left, W)) b :=
    fun i => congrFun (u i).2.choose_spec b
  simp only [e]
  rw [h, Pi.single_apply]
  by_cases hab : a = b
  · subst hab; simp
  · rw [if_neg (Ne.symm hab), if_neg hab]

end GlobalTheory.GcDual
