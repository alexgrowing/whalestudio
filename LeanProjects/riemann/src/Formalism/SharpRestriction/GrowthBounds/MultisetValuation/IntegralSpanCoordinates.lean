import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.LatAtZeroUpd

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset Formalism.MainNotions.G.LatticeSystems

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section Gen

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)

theorem upd_back (L : P.Tup) (w : Fin P.nV) (A1 : Submodule (P.W w) (Fin (P.m + 1) → P.Qq w)) :
    Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v))
      (Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L w A1) w (L w) = L := by
  exact (Function.update_idem (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) A1 (L w) L).trans
    (Function.update_eq_self (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) w L)

theorem upd_at (L : P.Tup) (w : Fin P.nV) (A1 : Submodule (P.W w) (Fin (P.m + 1) → P.Qq w)) :
    Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L w A1 w = A1 := by
  first
    | exact Function.update_self (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) w A1 L
    | exact Function.update_same (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) w A1 L

end Gen

theorem prod_zpow_upd {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] (x : K) (hx : x ≠ 0) (f g : ι → ℤ) (v : ι)
    (d : ℤ) (h1 : g v = f v + d) (h2 : ∀ u, u ≠ v → g u = f u) :
    ∏ u, x ^ (g u) = (∏ u, x ^ (f u)) * x ^ d := by
  rw [← Finset.mul_prod_erase Finset.univ (fun u => x ^ g u) (Finset.mem_univ v),
    ← Finset.mul_prod_erase Finset.univ (fun u => x ^ f u) (Finset.mem_univ v)]
  have hprod : ∏ u ∈ Finset.univ.erase v, x ^ g u = ∏ u ∈ Finset.univ.erase v, x ^ f u :=
    Finset.prod_congr rfl (fun u hu => by rw [h2 u (Finset.ne_of_mem_erase hu)])
  rw [hprod, h1, zpow_add₀ hx]
  ring

variable {p : ℕ} [Fact p.Prime] {X : Sys p} (Y : Pend X)

def hv (X : Sys p) (v : X.Pl) : ℤ := ((X.G.P.n' v / 2 : ℕ) : ℤ)

def Traw (j : ℕ) (s1 s2 : X.G.Kf) (Ξ : MvPowerSeries (X.ZA j) Y.Kc) (G : (X.Pj j).Xsp) : XspC (X.Pj (j + 1)) Y.Kc :=
  s1 • Y.DelF j G (s2 • Ξ)

theorem Traw_mul (j : ℕ) (s1 s2 c1 c2 : X.G.Kf) (Ξ : MvPowerSeries (X.ZA j) Y.Kc) (G : (X.Pj j).Xsp) :
    Traw Y j (s1 * c1) (s2 * c2) Ξ G = (c1 * c2) • Traw Y j s1 s2 Ξ G := by
  unfold Traw
  rw [mul_comm s2 c2, mul_smul c2 s2, map_smul, smul_smul, smul_smul]
  congr 1
  ring

def T0 (a a' : X.G.Kf) (v : X.Pl) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1))
    (f : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v) → ℚ) (G : (X.Pj j).Xsp) :
    XspC (X.Pj (j + 1)) Y.Kc :=
  Traw Y j (Y.eS j La * (Y.eT j La')⁻¹)
    (a ^ (Y.len v j La.2) * a' ^ (Y.len v (j + 1) La'.2) * (p : X.G.Kf) ^ (-(hv X v * Y.volE v j La.2 La'.2)))
    (Y.Xi v j (Y.aw v j La La') f) G

theorem integral_span_coordinates (a a' : X.G.Kf) (v : X.Pl) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) {ι : Type} (s : Finset ι)
    (f : ι → Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v) → ℚ) (G : (X.Pj j).Xsp) :
    T0 Y a a' v j La La' (∑ x ∈ s, f x) G = ∑ x ∈ s, T0 Y a a' v j La La' (f x) G := by
  unfold T0 Traw
  rw [map_sum, Finset.smul_sum, map_sum, Finset.smul_sum]

theorem kernel_nsmul (a a' : X.G.Kf) (v : X.Pl) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) (n : ℕ)
    (f : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v) → ℚ) (G : (X.Pj j).Xsp) :
    T0 Y a a' v j La La' (n • f) G = (n : X.G.Kf) • T0 Y a a' v j La La' f G := by
  unfold T0 Traw
  rw [map_nsmul, smul_comm _ n, map_nsmul, smul_comm _ n, Nat.cast_smul_eq_nsmul]

def cA (X : Sys p) (a' : X.G.Kf) (v : X.Pl) (j i : ℕ) : X.G.Kf :=
  (p : X.G.Kf) ^ (X.vm v (j + 1) * i) * (a' ^ (-(i : ℤ)) * (p : X.G.Kf) ^ (hv X v * (NN X.G.P.m X.t j : ℤ) * i))

def cC (X : Sys p) (a : X.G.Kf) (v : X.Pl) (j k : ℕ) : X.G.Kf :=
  (p : X.G.Kf) ^ (X.vm v (j + 1) * k) * (a ^ (k : ℤ) * (p : X.G.Kf) ^ (hv X v * (NN X.G.P.m X.t (j + 1) : ℤ) * k))

theorem kernel_target_identity (hp : (p : X.G.Kf) ≠ 0) (a a' : X.G.Kf) (ha' : a' ≠ 0) (v : X.Pl) (j : ℕ) (La : X.Lt j)
    (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup) (i : ℕ)
    (L1 : Submodule ((X.Pj (j + 1)).W (X.vJ (j + 1) v)) (Fin ((X.Pj (j + 1)).m + 1) → (X.Pj (j + 1)).Qq (X.vJ (j + 1) v)))
    (hE : IsEdge p ((X.Pj (j + 1)).n' (X.vJ (j + 1) v)) i ⟨L1, L' (X.vJ (j + 1) v)⟩)
    (f : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v) → ℚ) (G : (X.Pj j).Xsp) :
    T0 Y a a' v j La (c', Function.update L' (X.vJ (j + 1) v) L1) f G =
      cA X a' v j i • T0 Y a a' v j La (c', L') f G := by
  have e1 : Y.len v (j + 1) (Function.update L' (X.vJ (j + 1) v) L1) = Y.len v (j + 1) L' - i := by
    have := Y.len_edge (j + 1) (X.vJ (j + 1) v) i L' L1 hE
    rwa [vB_vJ] at this
  have e2 : ∀ u, u ≠ v → Y.len u (j + 1) (Function.update L' (X.vJ (j + 1) v) L1) = Y.len u (j + 1) L' := by
    intro u hu
    exact Y.len_other (j + 1) (X.vJ (j + 1) v) u L' L1 (by rw [vB_vJ]; exact hu)
  have e3 : Y.eT j (c', Function.update L' (X.vJ (j + 1) v) L1) =
      Y.eT j (c', L') * (p : X.G.Kf) ^ (-(X.vm v (j + 1) * i)) := by
    unfold Pend.eT
    apply prod_zpow_upd _ hp _ _ v
    · show X.vm v (j + 1) * Y.len v (j + 1) (Function.update L' (X.vJ (j + 1) v) L1) = _
      rw [e1]; ring
    · intro u hu
      show X.vm u (j + 1) * Y.len u (j + 1) (Function.update L' (X.vJ (j + 1) v) L1) = _
      rw [e2 u hu]
  have e4 : Y.volE v j La.2 (Function.update L' (X.vJ (j + 1) v) L1) =
      Y.volE v j La.2 L' - (NN X.G.P.m X.t j : ℤ) * i := by
    unfold Pend.volE
    rw [e1]; ring
  have e5 := Y.aw_tgt v j La (c', L') L1
  unfold T0
  show Traw Y j (Y.eS j La * (Y.eT j (c', Function.update L' (X.vJ (j + 1) v) L1))⁻¹)
    (a ^ (Y.len v j La.2) * a' ^ (Y.len v (j + 1) (Function.update L' (X.vJ (j + 1) v) L1)) *
      (p : X.G.Kf) ^ (-(hv X v * Y.volE v j La.2 (Function.update L' (X.vJ (j + 1) v) L1))))
    (Y.Xi v j (Y.aw v j La (c', Function.update L' (X.vJ (j + 1) v) L1)) f) G = _
  rw [e5, e3, e1, e4]
  have s1 : Y.eS j La * (Y.eT j (c', L') * (p : X.G.Kf) ^ (-(X.vm v (j + 1) * i)))⁻¹ =
      (Y.eS j La * (Y.eT j (c', L'))⁻¹) * (p : X.G.Kf) ^ (X.vm v (j + 1) * i) := by
    rw [mul_inv, ← zpow_neg, neg_neg, mul_assoc]
  have s2 : a ^ (Y.len v j La.2) * a' ^ (Y.len v (j + 1) L' - i) *
      (p : X.G.Kf) ^ (-(hv X v * (Y.volE v j La.2 L' - (NN X.G.P.m X.t j : ℤ) * i))) =
      (a ^ (Y.len v j La.2) * a' ^ (Y.len v (j + 1) L') * (p : X.G.Kf) ^ (-(hv X v * Y.volE v j La.2 L'))) *
        (a' ^ (-(i : ℤ)) * (p : X.G.Kf) ^ (hv X v * (NN X.G.P.m X.t j : ℤ) * i)) := by
    rw [sub_eq_add_neg, zpow_add₀ ha',
      show -(hv X v * (Y.volE v j La.2 L' - (NN X.G.P.m X.t j : ℤ) * i)) =
        -(hv X v * Y.volE v j La.2 L') + hv X v * (NN X.G.P.m X.t j : ℤ) * i by ring, zpow_add₀ hp]
    ring
  rw [s1, s2, Traw_mul]
  rfl

theorem kernel_source_identity (hp : (p : X.G.Kf) ≠ 0) (a a' : X.G.Kf) (ha : a ≠ 0) (v : X.Pl) (j : ℕ) (La : X.Lt j)
    (La' : X.Lt (j + 1)) (k : ℕ)
    (A1 : Submodule ((X.Pj j).W (X.vJ j v)) (Fin ((X.Pj j).m + 1) → (X.Pj j).Qq (X.vJ j v)))
    (hE : IsEdge p ((X.Pj j).n' (X.vJ j v)) k ⟨La.2 (X.vJ j v), A1⟩)
    (f : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v) → ℚ) (G : (X.Pj j).Xsp) :
    T0 Y a a' v j (La.1, Function.update La.2 (X.vJ j v) A1) La' f G =
      cC X a v j k • T0 Y a a' v j La La' f G := by
  have e1 : Y.len v j (Function.update La.2 (X.vJ j v) A1) = Y.len v j La.2 + k := by
    have := Y.len_edge j (X.vJ j v) k (Function.update La.2 (X.vJ j v) A1) (La.2 (X.vJ j v))
      (by rw [upd_at]; exact hE)
    rw [vB_vJ, upd_back] at this
    linarith
  have e2 : ∀ u, u ≠ v → Y.len u j (Function.update La.2 (X.vJ j v) A1) = Y.len u j La.2 := by
    intro u hu
    exact Y.len_other j (X.vJ j v) u La.2 A1 (by rw [vB_vJ]; exact hu)
  have e3 : Y.eS j (La.1, Function.update La.2 (X.vJ j v) A1) =
      Y.eS j La * (p : X.G.Kf) ^ (X.vm v (j + 1) * k) := by
    unfold Pend.eS
    apply prod_zpow_upd _ hp _ _ v
    · show X.vm v (j + 1) * Y.len v j (Function.update La.2 (X.vJ j v) A1) = _
      rw [e1]; ring
    · intro u hu
      show X.vm u (j + 1) * Y.len u j (Function.update La.2 (X.vJ j v) A1) = _
      rw [e2 u hu]
  have e4 : Y.volE v j (Function.update La.2 (X.vJ j v) A1) La'.2 =
      Y.volE v j La.2 La'.2 - (NN X.G.P.m X.t (j + 1) : ℤ) * k := by
    unfold Pend.volE
    rw [e1]; ring
  have e5 := Y.weight_update_at_place v j La La' A1
  unfold T0
  show Traw Y j (Y.eS j (La.1, Function.update La.2 (X.vJ j v) A1) * (Y.eT j La')⁻¹)
    (a ^ (Y.len v j (Function.update La.2 (X.vJ j v) A1)) * a' ^ (Y.len v (j + 1) La'.2) *
      (p : X.G.Kf) ^ (-(hv X v * Y.volE v j (Function.update La.2 (X.vJ j v) A1) La'.2)))
    (Y.Xi v j (Y.aw v j (La.1, Function.update La.2 (X.vJ j v) A1) La') f) G = _
  rw [e5, e3, e1, e4]
  have s1 : Y.eS j La * (p : X.G.Kf) ^ (X.vm v (j + 1) * k) * (Y.eT j La')⁻¹ =
      (Y.eS j La * (Y.eT j La')⁻¹) * (p : X.G.Kf) ^ (X.vm v (j + 1) * k) := by ring
  have s2 : a ^ (Y.len v j La.2 + k) * a' ^ (Y.len v (j + 1) La'.2) *
      (p : X.G.Kf) ^ (-(hv X v * (Y.volE v j La.2 La'.2 - (NN X.G.P.m X.t (j + 1) : ℤ) * k))) =
      (a ^ (Y.len v j La.2) * a' ^ (Y.len v (j + 1) La'.2) * (p : X.G.Kf) ^ (-(hv X v * Y.volE v j La.2 La'.2))) *
        (a ^ (k : ℤ) * (p : X.G.Kf) ^ (hv X v * (NN X.G.P.m X.t (j + 1) : ℤ) * k)) := by
    rw [zpow_add₀ ha,
      show -(hv X v * (Y.volE v j La.2 La'.2 - (NN X.G.P.m X.t (j + 1) : ℤ) * k)) =
        -(hv X v * Y.volE v j La.2 La'.2) + hv X v * (NN X.G.P.m X.t (j + 1) : ℤ) * k by ring, zpow_add₀ hp]
    ring
  rw [s1, s2, Traw_mul]
  rfl

end Formalism.MainNotions.FormalGroupSystem.Pf
