import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LogChain

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

section VF

variable {k : Type} [CommRing k] {τ : Type} [Fintype τ]

def vf (c : τ → MvPowerSeries τ k) (G : MvPowerSeries τ k) : MvPowerSeries τ k := ∑ t, c t * pderiv k t G

theorem vf_add (c : τ → MvPowerSeries τ k) (f G : MvPowerSeries τ k) : vf c (f + G) = vf c f + vf c G := by
  simp only [vf, map_add, mul_add, Finset.sum_add_distrib]

theorem vf_sub (c : τ → MvPowerSeries τ k) (f G : MvPowerSeries τ k) : vf c (f - G) = vf c f - vf c G := by
  simp only [vf, map_sub, mul_sub, Finset.sum_sub_distrib]

theorem vf_sum {ι : Type} (s : Finset ι) (c : τ → MvPowerSeries τ k) (f : ι → MvPowerSeries τ k) :
    vf c (∑ i ∈ s, f i) = ∑ i ∈ s, vf c (f i) := by
  simp only [vf, map_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem vf_C (c : τ → MvPowerSeries τ k) (a : k) : vf c (C a) = 0 := by
  simp [vf, MvPowerSeries.pderiv_C]

theorem vf_zeroc (G : MvPowerSeries τ k) : vf (fun _ => (0 : MvPowerSeries τ k)) G = 0 := by
  simp [vf]

theorem vf_mul (c : τ → MvPowerSeries τ k) (f G : MvPowerSeries τ k) :
    vf c (f * G) = vf c f * G + f * vf c G := by
  simp only [vf, Derivation.leibniz, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => by ring

theorem vf_X (c : τ → MvPowerSeries τ k) (s : τ) : vf c (X s) = c s := by
  classical
  simp [vf, MvPowerSeries.pderiv_X, Pi.single_apply]

end VF

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem liftX_hs : HasSubst (fun p : Fin 1 × Fin d => (X (Sum.inl p.2) : AA k d)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _

def liftHom : PS k 1 d →+* AA k d := (substAlgHom (liftX_hs (d := d) k)).toRingHom

theorem liftHom_apply (f : PS k 1 d) : liftHom k f = liftX k f := by
  simp only [liftHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPowerSeries.substAlgHom_apply]
  rfl

theorem liftX_zero : liftX k (0 : PS k 1 d) = 0 := by
  rw [← liftHom_apply, map_zero]

theorem liftX_mul (f g : PS k 1 d) : liftX k (f * g) = liftX k f * liftX k g := by
  simp only [← liftHom_apply, map_mul]

theorem liftX_sum {ι : Type} (s : Finset ι) (f : ι → PS k 1 d) :
    liftX k (∑ i ∈ s, f i) = ∑ i ∈ s, liftX k (f i) := by
  simp only [← liftHom_apply, map_sum]

theorem pderiv_inl_liftX (f : PS k 1 d) (j : Fin d) :
    pderiv k (Sum.inl j) (liftX k f) = liftX k (pderiv k ((0 : Fin 1), j) f) := by
  classical
  unfold liftX
  rw [LogPf.pderiv_subst (fun _ => MvPowerSeries.constantCoeff_X _) f (Sum.inl j)]
  rw [Finset.sum_eq_single ((0 : Fin 1), j)]
  · simp [MvPowerSeries.pderiv_X]
  · intro p _ hp
    have hp' : p.2 ≠ j := by
      intro h
      exact hp (Prod.ext (Subsingleton.elim _ _) h)
    simp [MvPowerSeries.pderiv_X, Pi.single_apply, hp']
  · simp

theorem pderiv_inr_liftX (f : PS k 1 d) (i : Fin d) : pderiv k (Sum.inr i) (liftX k f) = 0 := by
  classical
  unfold liftX
  rw [LogPf.pderiv_subst (fun _ => MvPowerSeries.constantCoeff_X _) f (Sum.inr i)]
  simp [MvPowerSeries.pderiv_X, Pi.single_apply]

def cf (B : FB R d O) (h : PS k 2 d) (u φ : Fin d → k) : Fin d ⊕ Fin d → AA k d :=
  Sum.elim (fun j => liftX k (∑ i : Fin d, C (u i) * ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), i) (B.FK k j))))
    (fun i => liftX k (Dof (B.FK k) u (sgOf k h i)) + C (φ i))

def fm (h : PS k 2 d) (u : Fin d → k) : AA k d := ∑ i : Fin d, (X (Sum.inr i) - liftX k (sgOf k h i)) * C (u i)

theorem cf_inl (B : FB R d O) (h : PS k 2 d) (u φ : Fin d → k) (j : Fin d) :
    cf k B h u φ (Sum.inl j) =
      liftX k (∑ i : Fin d, C (u i) * ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), i) (B.FK k j))) := rfl

theorem cf_inr (B : FB R d O) (h : PS k 2 d) (u φ : Fin d → k) (i : Fin d) :
    cf k B h u φ (Sum.inr i) = liftX k (Dof (B.FK k) u (sgOf k h i)) + C (φ i) := rfl

theorem nabla_eq (B : FB R d O) (h : PS k 2 d) (m : ℕ) (u φ : Fin d → k) (G : AA k d) :
    nabla k B h m u φ G = vf (cf k B h u φ) G - (C (m : k) * fm k h u) * G := by
  unfold nabla vf fm Dx
  rw [Fintype.sum_sum_type]
  simp only [cf_inl, cf_inr, add_mul, Finset.sum_add_distrib]
  ring

theorem vf_cf_liftX (B : FB R d O) (h : PS k 2 d) (u φ : Fin d → k) (g : PS k 1 d) :
    vf (cf k B h u φ) (liftX k g) = liftX k (Dof (B.FK k) u g) := by
  unfold vf
  rw [Fintype.sum_sum_type]
  simp only [cf_inl, pderiv_inl_liftX, pderiv_inr_liftX, mul_zero, Finset.sum_const_zero, add_zero]
  unfold Dof
  rw [liftX_sum]
  simp only [liftX_mul]

theorem connection_kills_series : ConnectionKillsSeries := by
  intro R _ d O _ _ k _ _ _ B h m φ f
  rw [nabla_eq, vf_cf_liftX]
  simp [fm, Dof, liftX_zero]

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
