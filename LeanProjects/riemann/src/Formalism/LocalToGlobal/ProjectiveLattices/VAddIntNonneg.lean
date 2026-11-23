import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

noncomputable section

namespace Formalism.L2.Pj

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

section One

variable {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R]

structure IsVal (la : HeightOneSpectrum (𝓞 K)) (v : R → EReal) : Prop where
  zero : v 0 = ⊤
  ne_bot : ∀ r, v r ≠ ⊥
  add : ∀ r s, min (v r) (v s) ≤ v (r + s)
  smul : ∀ (a : K) r, a ≠ 0 → v (a • r) = (((vAdd la a : ℤ) : ℝ) : EReal) + v r
  mul : ∀ r s, v (r * s) = v r + v s

structure IsNormOn (C : Submodule K R) (σ : K →+* ℂ) (N : R → ℝ) : Prop where
  nonneg : ∀ f ∈ C, 0 ≤ N f
  defin : ∀ f ∈ C, N f = 0 → f = 0
  smul : ∀ (a : K), ∀ f ∈ C, N (a • f) = ‖σ a‖ * N f
  add : ∀ f ∈ C, ∀ g ∈ C, N (f + g) ≤ N f + N g

theorem vAdd_int_nonneg (la : HeightOneSpectrum (𝓞 K)) {a : 𝓞 K} (ha : (a : K) ≠ 0) : 0 ≤ vAdd la (a : K) := by
  unfold vAdd
  have h1 := la.valuation_le_one (K := K) a
  have h2 : (la.valuation K) (a : K) ≠ 0 := (Valuation.ne_zero_iff _).mpr ha
  have h3 := (WithZero.log_le_log h2 one_ne_zero).mpr h1
  rw [WithZero.log_one] at h3
  omega

variable [Algebra (𝓞 K) R] [IsScalarTower (𝓞 K) K R]

def latOf (C : Submodule K R) (Vs : HeightOneSpectrum (𝓞 K) → Set (R → EReal))
    (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v) : Submodule (𝓞 K) C where
  carrier := {F | ∀ la, ∀ v ∈ Vs la, 0 ≤ v F}
  zero_mem' := fun la v hv => by
    change 0 ≤ v 0
    rw [(hV la v hv).zero]; exact le_top
  add_mem' := fun {F F'} hF hF' la v hv => (le_min (hF la v hv) (hF' la v hv)).trans ((hV la v hv).add _ _)
  smul_mem' := fun a F hF la v hv => by
    have h1 : ((a • F : C) : R) = (a : K) • (F : R) := (algebraMap_smul K a (F : R)).symm
    rw [h1]
    by_cases ha : (a : K) = 0
    · rw [ha, zero_smul, (hV la v hv).zero]; exact le_top
    · rw [(hV la v hv).smul _ _ ha]
      refine add_nonneg ?_ (hF la v hv)
      exact_mod_cast vAdd_int_nonneg la ha

end One

variable {D : D7}

abbrev Deg (D : D7) (j : ℕ) : Type :=
  (D.what₂.Tau → Fin (D.R.sigW j).1 → ℕ) × (D.what₂.Tau → Fin (D.R.sigW j).2 → ℕ) × ℕ

def deg {j : ℕ} (w : WeightFamilies.Wt D j) : Deg D j := (w.aP, w.aM, w.n)

theorem deg_inj {j : ℕ} : Function.Injective (deg (D := D) (j := j)) := by
  rintro ⟨a1, b1, _, _, n1, _⟩ ⟨a2, b2, _, _, n2, _⟩ h
  simp only [deg, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

theorem deg_wadd {j : ℕ} (w w' : WeightFamilies.Wt D j) : deg (WeightAlgebra.wadd w w') = deg w + deg w' := rfl

section Rec

variable {K : Type} [Field K] [NumberField K] (eO : 𝓞 K ≃+* D.what₂.O)
  {R : ℕ → Type} [∀ j, CommRing (R j)] [∀ j, Algebra K (R j)] [∀ j, Algebra (𝓞 K) (R j)]
  [∀ j, IsScalarTower (𝓞 K) K (R j)] (C : ∀ j, WeightFamilies.Wt D j → Submodule K (R j))

def cutR (j : ℕ) (w : WeightFamilies.Wt D j) : Submodule K (R j) := C j w ⊓ ⨅ _ : ¬ InR D j, ⊥

omit [NumberField K] [∀ j, Algebra (𝓞 K) (R j)] [∀ j, IsScalarTower (𝓞 K) K (R j)] in
theorem cutR_le (j : ℕ) (w : WeightFamilies.Wt D j) : cutR C j w ≤ C j w := inf_le_left

omit [NumberField K] [∀ j, Algebra (𝓞 K) (R j)] [∀ j, IsScalarTower (𝓞 K) K (R j)] in
theorem cutR_eq {j : ℕ} (h : InR D j) (w : WeightFamilies.Wt D j) : cutR C j w = C j w := by simp [cutR, h]

omit [NumberField K] [∀ j, Algebra (𝓞 K) (R j)] [∀ j, IsScalarTower (𝓞 K) K (R j)] in
theorem cutR_out {j : ℕ} (h : ¬ InR D j) (w : WeightFamilies.Wt D j) : cutR C j w = ⊥ := by simp [cutR, h]

omit [NumberField K] [∀ j, Algebra (𝓞 K) (R j)] [∀ j, IsScalarTower (𝓞 K) K (R j)] in
theorem cutR_zero {j : ℕ} (h : ¬ InR D j) {w : WeightFamilies.Wt D j} (F : cutR C j w) : F = 0 := by
  apply Subtype.ext
  have := F.2
  simpa [cutR_out C h w] using this

open Classical in

def cutN (N : ∀ j, WeightFamilies.Wt D j → (K →+* ℂ) → R j → ℝ) (j : ℕ) (w : WeightFamilies.Wt D j) (σ : K →+* ℂ)
    (F : cutR C j w) : ℝ := if InR D j then N j w σ F else 0

section Norm

variable {C} {N : ∀ j, WeightFamilies.Wt D j → (K →+* ℂ) → R j → ℝ}
  (hN : ∀ j, InR D j → ∀ w σ, IsNormOn (C j w) σ (N j w σ))
include hN

omit [∀ j, Algebra (𝓞 K) (R j)] [∀ j, IsScalarTower (𝓞 K) K (R j)]

theorem cutN_nonneg (j w σ) (F : cutR C j w) : 0 ≤ cutN C N j w σ F := by
  unfold cutN; split_ifs with h
  · exact (hN j h w σ).nonneg _ (cutR_le C j w F.2)
  · exact le_rfl

theorem cutN_smul (j w σ) (a : K) (F : cutR C j w) : cutN C N j w σ (a • F) = ‖σ a‖ * cutN C N j w σ F := by
  unfold cutN; split_ifs with h
  · exact (hN j h w σ).smul a _ (cutR_le C j w F.2)
  · simp

theorem cutN_eq_zero (j w σ) (F : cutR C j w) : cutN C N j w σ F = 0 ↔ F = 0 := by
  constructor
  · intro h0
    by_cases h : InR D j
    · unfold cutN at h0; rw [if_pos h] at h0
      exact Subtype.ext ((hN j h w σ).defin _ (cutR_le C j w F.2) h0)
    · exact cutR_zero C h F
  · rintro rfl
    have := cutN_smul hN j w σ 0 0
    simpa using this

theorem cutN_add (j w σ) (F G : cutR C j w) : cutN C N j w σ (F + G) ≤ cutN C N j w σ F + cutN C N j w σ G := by
  unfold cutN; split_ifs with h
  · exact (hN j h w σ).add _ (cutR_le C j w F.2) _ (cutR_le C j w G.2)
  · simp

end Norm

variable (hfd : ∀ j, InR D j → ∀ w, FiniteDimensional K (C j w))
  (Vs : ∀ j, HeightOneSpectrum (𝓞 K) → Set (R j → EReal)) (hV : ∀ j la, ∀ v ∈ Vs j la, IsVal la v)
  (Ns Nl : ∀ j, WeightFamilies.Wt D j → (K →+* ℂ) → R j → ℝ)
  (hNs : ∀ j, InR D j → ∀ w σ, IsNormOn (C j w) σ (Ns j w σ))
  (hNl : ∀ j, InR D j → ∀ w σ, IsNormOn (C j w) σ (Nl j w σ))
  (hle : ∀ j, InR D j → ∀ w σ, ∀ f ∈ C j w, Nl j w σ f ≤ Ns j w σ f)
  (Cu : ℕ → Type) (Xc : ∀ j, Cu j → Submodule (𝓞 D.host.E) (Fin (WeightFamilies.rho D j) → D.host.E))
  (hXc : ∀ j c, Submodule.IsLattice D.host.E (Xc j c))
  (FJ : ∀ j (c : Cu j), WeightFamilies.ExpoSet D (Xc j c) → WeightFamilies.Wt D j → Type)
  [∀ j c χ w, AddCommGroup (FJ j c χ w)] [∀ j c χ w, Module K (FJ j c χ w)]
  (sg : ∀ j (c : Cu j) (χ : WeightFamilies.ExpoSet D (Xc j c)) (w : WeightFamilies.Wt D j), C j w →ₗ[K] FJ j c χ w)

@[reducible] def mkB : WeightFamilies.Prov D where
  KO := K
  eO := eO
  Cusp j w := cutR C j w
  fdC j w := by
    by_cases h : InR D j
    · rw [cutR_eq C h]; exact hfd j h w
    · rw [cutR_out C h]; infer_instance
  Mlat j w := latOf (cutR C j w) (Vs j) (hV j)
  supN := cutN C Ns
  supN_nonneg := cutN_nonneg hNs
  supN_eq_zero := cutN_eq_zero hNs
  supN_smul := cutN_smul hNs
  supN_add := cutN_add hNs
  l2NormAlt := cutN C Nl
  l2Norm_nonneg_bis := cutN_nonneg hNl
  l2Norm_eq_zero_iff := cutN_eq_zero hNl
  l2Norm_smul_alt := cutN_smul hNl
  l2Norm_add_le' := cutN_add hNl
  l2Norm_le_supNorm_alt j w σ F := by
    unfold cutN; split_ifs with h
    · exact hle j h w σ _ (cutR_le C j w F.2)
    · exact le_rfl
  Cu := Cu
  Xc := Xc
  Xc_lat := hXc
  FJt := FJ
  sg j c χ w := (sg j c χ w).comp (Submodule.inclusion (cutR_le C j w))

def spanIn (j : ℕ) (w : WeightFamilies.Wt D j) (s : Set (R j)) : Submodule (𝓞 K) (cutR C j w) :=
  (Submodule.span (𝓞 K) s).comap ((cutR C j w).subtype.restrictScalars (𝓞 K))

def mkX (P : ModuliIntegralCharts.Prov D) (j : ℕ) (hj : InR D j)
    (hmul : ∀ w w', ∀ f ∈ C j w, ∀ g ∈ C j w', f * g ∈ C j (WeightAlgebra.wadd w w'))
    (dat : P.Dat) (hrk : j < D.R.m → P.rk dat = D.R.r) (hjj : j < D.R.m → P.jj dat = (D.R.sigW j).1)
    (Pt : HeightOneSpectrum (𝓞 K) → Type)
    (p66 : ∀ la, Pt la → (P.loc dat (WeightAlgebra.resCh la)).Pt (P.loc dat (WeightAlgebra.resCh la)).YY)
    (pv : ∀ la, Pt la → R j → EReal) (hpv : ∀ la y, IsVal la (pv la y))
    (hlat : ∀ w, ∀ f ∈ C j w, (∀ la, ∀ v ∈ Vs j la, 0 ≤ v f) ↔ ∀ la y, 0 ≤ pv la y f)
    (th sh : WeightFamilies.Wt D j → Set (R j)) :
    WeightAlgebra.PJ D (mkB eO C hfd Vs hV Ns Nl hNs hNl hle Cu Xc hXc FJ sg) P j where
  Forms := AddMonoidAlgebra (R j) (Deg D j)
  inc w := incG deg (cutR C j) w
  inc_inj w := incG_inj deg (cutR C j) w
  inc_indep := incG_indep deg (cutR C j) deg_inj
  inc_mul w w' F G :=
    ⟨⟨_, by rw [cutR_eq C hj]; exact hmul w w' _ (cutR_le C j w F.2) _ (cutR_le C j w' G.2)⟩,
      incG_mul deg (cutR C j) (deg_wadd w w') F G _⟩
  dat := dat
  dat_rk := hrk
  dat_jj := hjj
  Pt := Pt
  pt66 := p66
  vAt la y := vG (pv la y)
  vAt_zero la y := vG_zero (hpv la y).zero
  vAt_ne_bot la y := vG_ne_bot (hpv la y).zero (hpv la y).ne_bot
  vAt_add la y := vG_add (hpv la y).add
  vAt_smul la y a F ha := vG_smul (fun r => (hpv la y).smul a r ha) F
  vAt_mul la y := vG_mul deg (cutR C j) (hpv la y).zero (hpv la y).mul
  Mlat_eq w F := by
    refine (hlat w _ (cutR_le C j w F.2)).trans (forall_congr' fun la => forall_congr' fun y => ?_)
    rw [vG_incG deg (cutR C j) (hpv la y).zero]
  thAll w := spanIn C j w (th w)
  shortTh w := spanIn C j w (sh w)

end Rec

end Formalism.L2.Pj
