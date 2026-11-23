import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionAlgebraCp

noncomputable section

namespace Formalism.L2.G.Pend

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem

variable {p : ℕ} [Fact p.Prime]

section K3

variable (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmb X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv)
    (be : MvPowerSeries (Fin 2) (K0 p))
    (ThF : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) ℂ_[p])
    (DelF : DelTy X E) (hDel : DelDeg X E DelF)

theorem condition_iff_additive_maps (D : Formalism.BasicNotions.D7) :
    Formalism.MainNotions.FormalGroupSystem.adm5 D X (pendOf X E hfin hst be ThF DelF hDel) ↔
      ∀ v, ∀ j < X.mm, letI := algKfC E; XiEx X ℂ_[p] ThF v j := by
  let _ := algKfC E
  constructor
  · intro h v j hj
    exact ⟨_, h v j hj⟩
  · intro h v j hj
    exact xiOf_spec X ℂ_[p] ThF (h v j hj)

theorem iC_int (x : (pendOf X E hfin hst be ThF DelF hDel).Kc) :
    x ∈ (pendOf X E hfin hst be ThF DelF hDel).Oc ↔ ‖(RingHom.id ℂ_[p]) x‖ ≤ 1 := Iff.rfl

end K3

section Rename

variable (X : Sys p) {T : Type} (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)

def kapOf (j : ℕ) (z : X.ZA j) : T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1) :=
  (pos ⟨z.1, z.2.1⟩, Fin.cast (rank_eq X (j + 1)).symm z.2.2.2, Fin.cast (rank_eq X j).symm z.2.2.1)

def thFOf (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])
    (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) : MvPowerSeries (X.ZA j) ℂ_[p] :=
  resV (kapOf X pos j) (F j La La')

theorem thFOf_coeff
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])
    (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) (n : X.ZA j →₀ ℕ) :
    (RingHom.id ℂ_[p]) (MvPowerSeries.coeff n (thFOf X pos F j La La')) =
      MvPowerSeries.coeff (n.mapDomain fun z : X.ZA j =>
        (pos ⟨z.1, z.2.1⟩, Fin.cast (rank_eq X (j + 1)).symm z.2.2.2, Fin.cast (rank_eq X j).symm z.2.2.1))
        (F j La La') := rfl

theorem kapOf_injective (j : ℕ) : Function.Injective (kapOf X pos j) := by
  rintro ⟨v, s, a, b⟩ ⟨v', s', a', b'⟩ h
  simp only [kapOf, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq, Fin.cast_inj] at h
  obtain ⟨h1, h2, h3⟩ := h
  cases h1
  subst h2 h3
  rfl

end Rename

def Compat (G : GAtP p) (E : CEmb G) (rd : ∀ v, G.P.W v →+* WW p) : Prop :=
  ∀ (v : Fin G.P.nV) (s : ℕ) (x : G.P.W v),
    E.iK (G.P.ι v ((G.P.σ v ^ s) (algebraMap (G.P.W v) (G.P.Qq v) x))) =
      k0ToC p (algebraMap (WW p) (K0 p) ((sigW p)^[s] (rd v x)))

section Conc

variable {n : ℕ} (L : IntermediateField (KO p n) (Om p n)) [FiniteDimensional (KO p n) L]

def rdW (p : ℕ) [Fact p.Prime] (n : ℕ) : WQ p n →+* WW p := (gWW p n).comp (jW p n)

theorem rdW_frob (x : WQ p n) : rdW p n (WittVector.frobenius x) = sigW p (rdW p n x) := by
  ext k
  simp only [rdW, gWW, jW, sigW, RingHom.comp_apply, WittVector.map_coeff, WittVector.coeff_frobenius_charP, map_pow]

theorem rdW_frob_iter (s : ℕ) (x : WQ p n) : rdW p n ((WittVector.frobenius^[s]) x) = (sigW p)^[s] (rdW p n x) := by
  induction s generalizing x with
  | zero => rfl
  | succ s ih => rw [Function.iterate_succ_apply, ih, rdW_frob, ← Function.iterate_succ_apply]

theorem iota_alg (x : WQ p n) : iota p n (algebraMap (WQ p n) (QQ p n) x) = algebraMap (OO p n) (KO p n) (jO p n x) :=
  IsFractionRing.lift_algebraMap (inj_WK p n) x

theorem compat_conc (s : ℕ) (x : WQ p n) :
    embLC (k0ToC p) L (algebraMap (KO p n) L (iota p n ((sig p n ^ s) (algebraMap (WQ p n) (QQ p n) x)))) =
      k0ToC p (algebraMap (WW p) (K0 p) ((sigW p)^[s] (rdW p n x))) := by
  rw [sig_pow_alg, iota_alg, ← IsScalarTower.algebraMap_apply (OO p n) (KO p n) L, ← rdW_frob_iter]
  show iC (k0ToC p) (gL L _) = _
  rw [gL_jO, iC_alg]
  rfl

theorem embLC_int' (x : OL p n L) : ‖embLC (k0ToC p) L (algebraMap (OL p n L) L x)‖ ≤ 1 :=
  embLC_int (k0ToC p) (fun y => by rw [witt_fraction_to_Cp_algebraMap]; exact norm_wToC_le p y) L x

end Conc

end Formalism.L2.G.Pend
