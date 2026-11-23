import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibCon

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob

private lemma zd_comm {K : Type} [Field K] {Δ : K} {z : DX Δ} (hz : z ∈ ZD Δ) (g : DX Δ) : z * g = g * z := by
  obtain ⟨a, ha⟩ := Subgroup.mem_subgroupOf.1 hz
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha]
  apply Units.ext
  simp only [MonoidHom.comp_apply, Units.val_mul]
  exact (Matrix.scalar_commute _ (fun r => Commute.all _ _) _).eq

private lemma conj_sup {G : Type} [Group G] (Z J : Subgroup G) (f : G → ℂ)
    (hZ : ∀ z ∈ Z, ∀ g, z * g = g * z) (hJ : ∀ u ∈ J, ∀ g, f (u⁻¹ * g * u) = f g) :
    ∀ u ∈ Z ⊔ J, ∀ g, f (u⁻¹ * g * u) = f g := by
  let S : Subgroup G :=
    { carrier := {u | ∀ g, f (u⁻¹ * g * u) = f g}
      one_mem' := by intro g; simp
      mul_mem' := by
        intro a b ha hb g
        have : (a * b)⁻¹ * g * (a * b) = b⁻¹ * (a⁻¹ * g * a) * b := by group
        rw [this, hb, ha]
      inv_mem' := by
        intro a ha g
        rw [← ha]
        congr 1
        group }
  have h : Z ⊔ J ≤ S := by
    refine sup_le (fun z hz g => ?_) (fun u hu => hJ u hu)
    rw [mul_assoc, ← hZ z hz, inv_mul_cancel_left]
  exact fun u hu => h hu

theorem UpperTheory.orbitalFiber_fixedSet_conj :
    UpperTheory.V.Z.Sym.Glob.Fib.FSConj := by
  intro F _ _ Δ D hD t ht u hu g
  unfold Dat.FS
  refine finprod_congr fun v => ?_
  have huv : u.1 v ∈ ZD _ ⊔ D.J2v v := by
    simp only [Dat.UZ, RPG.box, Subgroup.mem_iInf, Subgroup.mem_comap] at hu
    exact hu v
  show D.fSv t v ((u.1 v)⁻¹ * g.1 v * u.1 v) = D.fSv t v (g.1 v)
  refine conj_sup _ _ (D.fSv t v) (fun z hz => zd_comm hz) ?_ _ huv _
  intro k hk y
  unfold Dat.fSv
  unfold Dat.J2v at hk
  by_cases hv : v ∈ D.Sg
  · simp only [if_pos hv] at hk ⊢
    have H := (hD.sig v hv).S_inv (t v) (ht v hv)
    rw [(H k hk _).2, (H _ (inv_mem hk) _).1]
  · simp only [if_neg hv] at hk ⊢
    congr 1
    apply propext
    rw [Subgroup.mul_mem_cancel_right _ hk, Subgroup.mul_mem_cancel_left _ (inv_mem hk)]
