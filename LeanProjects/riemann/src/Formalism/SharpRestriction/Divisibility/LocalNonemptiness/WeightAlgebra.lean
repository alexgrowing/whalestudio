import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.WeightFamilies

noncomputable section

namespace Formalism.MainNotions.DIV.Inh

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions

theorem nonempty_kappa_hypothesis : Nonempty WeightAlgebra.KHyp := ⟨⟨0, 0, 0, 0, 0, 0, 0⟩⟩

theorem nonempty_kappa_admissible : Nonempty WeightAlgebra.KAdm := ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩

theorem nonempty_scalars (D : D7) (B : WeightFamilies.Prov D) : Nonempty (WeightAlgebra.Scal B) := ⟨⟨1, 1, 1, 1⟩⟩

def HasDat {D : D7} (P : ModuliIntegralCharts.Prov D) (j : ℕ) : Prop :=
  ∃ dat : P.Dat, (j < D.R.m → P.rk dat = D.R.r) ∧ (j < D.R.m → P.jj dat = (D.R.sigW j).1)

def CuspZero {D : D7} (B : WeightFamilies.Prov D) (j : ℕ) : Prop := ∀ w, Subsingleton (B.Cusp j w)

def toyPjOfCuspZero {D : D7} (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (hB : CuspZero B j) (dat : P.Dat)
    (h1 : j < D.R.m → P.rk dat = D.R.r) (h2 : j < D.R.m → P.jj dat = (D.R.sigW j).1) : WeightAlgebra.PJ D B P j where
  Forms := B.KO
  inc := fun _ => 0
  inc_inj := fun w a b _ => (hB w).elim a b
  inc_indep := by
    have : (fun w : WeightFamilies.Wt D j => LinearMap.range (0 : B.Cusp j w →ₗ[B.KO] B.KO)) = fun _ => ⊥ := by
      funext w; exact LinearMap.range_zero
    rw [this]
    intro w
    exact disjoint_bot_left
  inc_mul := fun _ _ _ _ => ⟨0, by simp⟩
  dat := dat
  dat_rk := h1
  dat_jj := h2
  Pt := fun _ => Empty
  pt66 := fun _ y => y.elim
  vAt := fun _ y => y.elim
  vAt_zero := fun _ y => y.elim
  vAt_ne_bot := fun _ y => y.elim
  vAt_add := fun _ y => y.elim
  vAt_smul := fun _ y => y.elim
  vAt_mul := fun _ y => y.elim
  Mlat_eq := fun w F => ⟨fun _ _ y => y.elim, fun _ => by
    have : F = 0 := (hB w).elim _ _
    rw [this]; exact Submodule.zero_mem _⟩
  thAll := fun _ => ⊥
  shortTh := fun _ => ⊥

theorem nonempty_piece_of_cusp_zero (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (hB : CuspZero B j) (hP : HasDat P j) :
    Nonempty (WeightAlgebra.PJ D B P j) := by
  obtain ⟨dat, h1, h2⟩ := hP
  exact ⟨toyPjOfCuspZero B P j hB dat h1 h2⟩

theorem HasDat_of_PJ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j) : HasDat P j :=
  ⟨X.dat, X.dat_rk, X.dat_jj⟩

theorem isEmpty_piece_of_no_datum (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (h : IsEmpty P.Dat) :
    IsEmpty (WeightAlgebra.PJ D B P j) := ⟨fun X => h.elim X.dat⟩

theorem PJ_forces_Mlat {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j) (w : WeightFamilies.Wt D j)
    (h : Subsingleton (B.Cusp j (WeightAlgebra.wadd w w))) (F : B.Cusp j w) : F ∈ B.Mlat j w := by
  rw [X.Mlat_eq]
  intro la y
  obtain ⟨H, hH⟩ := X.inc_mul w w F F
  have h0 : H = 0 := Subsingleton.elim _ _
  have h1 := X.vAt_mul la y w w F F
  rw [hH, h0, map_zero, X.vAt_zero] at h1
  have ha : X.vAt la y (X.inc w F) = ⊤ := by
    by_contra hne
    exact EReal.add_ne_top hne hne h1.symm
  rw [ha]
  exact le_top

def provBad (D : D7) (K : Type) [Field K] [NumberField K] (e : 𝓞 K ≃+* D.what₂.O) : WeightFamilies.Prov D where
  KO := K
  eO := e
  Cusp := fun _ w => ((if w.n = 2 then ⊤ else ⊥ : Submodule K K) : Type)
  Mlat := fun _ _ => ⊥
  supN := fun _ _ σ F => ‖σ (F : K)‖
  supN_nonneg := fun _ _ _ _ => norm_nonneg _
  supN_eq_zero := fun _ _ σ F => by
    rw [norm_eq_zero, map_eq_zero]; exact Submodule.coe_eq_zero
  supN_smul := fun _ _ σ a F => by
    rw [Submodule.coe_smul, smul_eq_mul, map_mul, norm_mul]
  supN_add := fun _ _ σ F G => by
    rw [Submodule.coe_add, map_add]; exact norm_add_le _ _
  l2NormAlt := fun _ _ σ F => ‖σ (F : K)‖
  l2Norm_nonneg_bis := fun _ _ _ _ => norm_nonneg _
  l2Norm_eq_zero_iff := fun _ _ σ F => by
    rw [norm_eq_zero, map_eq_zero]; exact Submodule.coe_eq_zero
  l2Norm_smul_alt := fun _ _ σ a F => by
    rw [Submodule.coe_smul, smul_eq_mul, map_mul, norm_mul]
  l2Norm_add_le' := fun _ _ σ F G => by
    rw [Submodule.coe_add, map_add]; exact norm_add_le _ _
  l2Norm_le_supNorm_alt := fun _ _ _ _ => le_rfl
  Cu := fun _ => Empty
  Xc := fun _ c => c.elim
  Xc_lat := fun _ c => c.elim
  FJt := fun _ _ _ _ => PUnit
  sg := fun _ _ _ _ => 0

theorem exists_provision_empty_pieces (D : D7) (h : OsRingOfIntegers D) :
    ∃ B : WeightFamilies.Prov D, ∀ (P : ModuliIntegralCharts.Prov D) (j : ℕ), IsEmpty (WeightAlgebra.PJ D B P j) := by
  obtain ⟨K, _, _, ⟨e⟩⟩ := h
  refine ⟨provBad D K e, fun P j => ⟨fun X => ?_⟩⟩
  let w : WeightFamilies.Wt D j := WeightAlgebra.wscalar D j 2 ⟨1, rfl⟩
  have hs : Subsingleton ((provBad D K e).Cusp j (WeightAlgebra.wadd w w)) := by
    change Subsingleton ((if (2 + 2 : ℕ) = 2 then ⊤ else ⊥ : Submodule K K) : Type)
    rw [if_neg (by norm_num)]
    infer_instance
  let F : (provBad D K e).Cusp j w :=
    (⟨(1 : K), by rw [if_pos rfl]; trivial⟩ :
      ((if (2 : ℕ) = 2 then ⊤ else ⊥ : Submodule K K) : Type))
  have hF : F ∈ (provBad D K e).Mlat j w := PJ_forces_Mlat X w hs F
  have hF0 : F = 0 := (Submodule.mem_bot (𝓞 (provBad D K e).KO)).1 hF
  have : (1 : K) = 0 := congrArg (fun z : ((if (2 : ℕ) = 2 then ⊤ else ⊥ : Submodule K K) : Type) => (z : K)) hF0
  exact one_ne_zero this

def HasFullLocalData (D : D7) : Prop :=
  ∃ P : ModuliIntegralCharts.Prov D, ∀ r j, 1 ≤ j → j + 1 ≤ r → ∃ w : P.Dat, P.rk w = r ∧ P.jj w = j

theorem HasDat_of_full {D : D7} (P : ModuliIntegralCharts.Prov D)
    (hP : ∀ r j, 1 ≤ j → j + 1 ≤ r → ∃ w : P.Dat, P.rk w = r ∧ P.jj w = j) (j : ℕ) (h1 : 1 ≤ j) : HasDat P j := by
  have hk : 1 ≤ D.R.k := by
    have h2 := D.R.f_le_k
    have h3 : 0 < D.R.ord := D.R.ord_pos
    have h4 : D.R.f = 2 * D.R.ord := rfl
    omega
  by_cases hj : j < D.R.m
  · obtain ⟨w, hw1, hw2⟩ := hP D.R.r (D.R.sigW j).1
      (by simp only [Ranks.sigW]; omega) (by simp only [Ranks.sigW, Ranks.r]; omega)
    exact ⟨w, fun _ => hw1, fun _ => hw2⟩
  · obtain ⟨w, _, _⟩ := hP 2 1 le_rfl le_rfl
    exact ⟨w, fun h => absurd h hj, fun h => absurd h hj⟩

theorem nonempty_provision_of_cusp_zero (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (hB : ∀ j, CuspZero B j)
    (hP : ∀ j, 1 ≤ j → j ≤ D.R.m → HasDat P j) : Nonempty (WeightAlgebra.Prov D B P) :=
  ⟨fun j h1 h2 => (nonempty_piece_of_cusp_zero D B P j (hB j) (hP j h1 h2)).some⟩

theorem nonempty_provision (D : D7) (hO : OsRingOfIntegers D) (h66 : HasFullLocalData D) :
    ∃ (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D), Nonempty (WeightAlgebra.Prov D B P) := by
  obtain ⟨K, _, _, ⟨e⟩⟩ := hO
  obtain ⟨P, hP⟩ := h66
  exact ⟨zeroCuspModel D K e, P, nonempty_provision_of_cusp_zero D _ P (fun j w => zero_cusp_model_subsingleton D K e j w)
    (fun j h1 _ => HasDat_of_full P hP j h1)⟩

end Formalism.MainNotions.DIV.Inh

end
