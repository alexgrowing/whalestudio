import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.SimpleDistinctness.ScalarCharacterOfL2Embedding
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.KTypesAbove
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.GlobalTheory.ExistsExpUnitary

open Matrix Finset PI.UpqRep
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.RenumDS

variable {n : ℕ}

abbrev ren (r : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := g.submatrix r r

lemma ren_mul (r : Equiv.Perm (Fin n)) (g h : Matrix (Fin n) (Fin n) ℂ) : ren r (g * h) = ren r g * ren r h :=
  (Matrix.submatrix_mul_equiv g h r r r).symm

lemma ren_one (r : Equiv.Perm (Fin n)) : ren r (1 : Matrix (Fin n) (Fin n) ℂ) = 1 :=
  Matrix.submatrix_one_equiv r

lemma ren_ct (r : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) : (ren r g)ᴴ = ren r gᴴ :=
  Matrix.conjTranspose_submatrix g r r

lemma ren_ren_symm (r : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) : ren r (ren r.symm g) = g := by
  ext i j; simp [ren]

lemma ren_Jm (ε : Fin n → Bool) (r : Equiv.Perm (Fin n)) : Jm (ε ∘ r) = ren r (Jm ε) := by
  unfold Jm
  rw [ren, Matrix.submatrix_diagonal_equiv]
  rfl

lemma ren_diag (r : Equiv.Perm (Fin n)) (d : Fin n → ℂ) : ren r (diagonal d) = diagonal (d ∘ r) :=
  Matrix.submatrix_diagonal_equiv d r

lemma mem_K {ε : Fin n → Bool} (r : Equiv.Perm (Fin n)) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) :
    ren r g ∈ Kset (ε ∘ r) := by
  obtain ⟨hu, hc⟩ := hg
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hu ⊢
    rw [ren_ct, ← ren_mul, hu, ren_one]
  · rw [ren_Jm, ← ren_mul, ← ren_mul, hc]

lemma mem_UJ {ε : Fin n → Bool} (r : Equiv.Perm (Fin n)) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    ren r g ∈ UJset (ε ∘ r) := by
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  show (ren r g)ᴴ * Jm (ε ∘ r) * ren r g = Jm (ε ∘ r)
  rw [ren_ct, ren_Jm, ← ren_mul, ← ren_mul, hg']

lemma mem_inG {ε : Fin n → Bool} (r : Equiv.Perm (Fin n)) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    inG (ε ∘ r) (ren r X) := by
  have h' : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  show (ren r X)ᴴ * Jm (ε ∘ r) + Jm (ε ∘ r) * ren r X = 0
  rw [ren_ct, ren_Jm, ← ren_mul, ← ren_mul]
  have : ren r (Xᴴ * Jm ε) + ren r (Jm ε * X) = ren r (Xᴴ * Jm ε + Jm ε * X) := by
    ext i j; simp [ren]
  rw [this, h']
  ext i j; simp [ren]

lemma continuous_ren (r : Equiv.Perm (Fin n)) : Continuous (ren r) := by
  refine continuous_matrix fun i j => ?_
  exact (continuous_apply_apply (r i) (r j))

lemma exp_ren (r : Equiv.Perm (Fin n)) (X : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp (ren r X) = ren r (NormedSpace.exp X) := by
  have h := GlobalTheory.CompanionTheory.UnitaryExp.map_exp_matrix (Matrix.reindexAlgEquiv ℂ ℂ r.symm)
    ((continuous_ren r).congr (fun M => by ext i j; simp [ren])) X
  exact h.symm

def Ord (ε : Fin n → Bool) (r : Equiv.Perm (Fin n)) : Prop := ∀ a b, a < b → ε a = ε b → r a < r b

lemma Ord.symm {ε ε₁ : Fin n → Bool} {r : Equiv.Perm (Fin n)} (hε : ε₁ = ε ∘ r) (h : Ord ε₁ r) : Ord ε r.symm := by
  intro a b hab he
  by_contra hlt
  rcases (not_lt.1 hlt).lt_or_eq with h1 | h1
  · have := h _ _ h1 (by subst hε; simp [he])
    simp at this
    exact absurd hab (not_lt.2 this.le)
  · have := r.symm.injective h1
    exact absurd hab (by simp [this])

section Rep

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ε ε₁ : Fin n → Bool} {r : Equiv.Perm (Fin n)} {τ τ' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

lemma hε_symm (hε : ε₁ = ε ∘ r) : ε = ε₁ ∘ r.symm := by subst hε; ext a; simp

lemma hτ_symm (hτ : ∀ g, τ' g = τ (ren r g)) : ∀ g, τ g = τ' (ren r.symm g) := fun g => by
  rw [hτ, ren_ren_symm]

lemma stab_ren (hε : ε₁ = ε ∘ r) (hτ : ∀ g, τ' g = τ (ren r g)) {S : Submodule ℂ H}
    (h : IsKStableOn ε₁ τ S) : IsKStableOn ε τ' S := by
  subst hε
  intro g hg v hv
  rw [hτ]
  exact h _ (mem_K r hg) v hv

lemma kfin_ren (hε : ε₁ = ε ∘ r) (hτ : ∀ g, τ' g = τ (ren r g)) {v : H}
    (h : IsKFin ε₁ τ v) : IsKFin ε τ' v := by
  obtain ⟨S, h1, h2, h3⟩ := h
  exact ⟨S, h1, h2, stab_ren hε hτ h3⟩

lemma wt_ren (hε : ε₁ = ε ∘ r) (hτ : ∀ g, τ' g = τ (ren r g)) {μ : Fin n → ℝ} {v : H}
    (h : IsWtOn (Kset ε₁) τ μ v) : IsWtOn (Kset ε) τ' (μ ∘ r.symm) v := by
  subst hε
  intro θ hθ
  have hm := mem_K r hθ
  rw [ren_diag] at hm
  have h1 := h (θ ∘ r) hm
  rw [hτ, ren_diag]
  have e : (∑ a, (μ ∘ r.symm) a * θ a) = ∑ a, μ a * (θ ∘ r) a :=
    (Fintype.sum_equiv r _ _ (fun a => by simp)).symm
  rw [e]
  exact h1

lemma root_ren (r : Equiv.Perm (Fin n)) (a b x : Fin n) :
    root (r a) (r b) x = root a b (r.symm x) := by
  have hb : (x = r b) ↔ (r.symm x = b) := by
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  have ha : (x = r a) ↔ (r.symm x = a) := by
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  simp only [root, Pi.sub_apply, Pi.single_apply, hb, ha]

lemma cdom_ren (hε : ε₁ = ε ∘ r) (ho : Ord ε₁ r) {μ Λ : Fin n → ℝ} (h : CDom ε₁ μ Λ) :
    CDom ε (μ ∘ r.symm) (Λ ∘ r.symm) := by
  subst hε
  obtain ⟨c, hc, he⟩ := h
  refine ⟨fun a b => c (r.symm a) (r.symm b), fun a b hab => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hc _ _ hab
    have := ho _ _ h1 h2
    simp at this h2
    exact ⟨this, h2⟩
  · funext x
    have hx := congrFun he (r.symm x)
    simp only [Pi.sub_apply, Function.comp, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hx ⊢
    rw [hx]
    refine (Fintype.sum_equiv r _ _ (fun a => ?_))
    refine (Fintype.sum_equiv r _ _ (fun b => ?_))
    rw [root_ren]
    simp

lemma kType_ren (hε : ε₁ = ε ∘ r) (ho : Ord ε₁ r) (hτ : ∀ g, τ' g = τ (ren r g)) {Λ : Fin n → ℝ}
    {S : Submodule ℂ H} (h : IsKTypeOf ε₁ τ Λ S) : IsKTypeOf ε τ' (Λ ∘ r.symm) S := by
  obtain ⟨h1, h2, h3, ⟨v, hv, hne, hw⟩, h5⟩ := h
  refine ⟨h1, stab_ren hε hτ h2, fun S' hS' hst => h3 S' hS' (stab_ren (hε_symm hε) (hτ_symm hτ) hst),
    ⟨v, hv, hne, wt_ren hε hτ hw⟩, fun μ w hw1 hw2 hw3 => ?_⟩
  have h6 := h5 _ w hw1 hw2 (wt_ren (hε_symm hε) (hτ_symm hτ) hw3)
  have h7 := cdom_ren hε ho h6
  convert h7 using 1
  ext a; simp

open Formalism.REAL (GlRel IsUnitary KHighest IsWeight sgn)
open CompanionTheory.D.LK (IsKMod LocFin)
open CompanionTheory.D.DSIC (KStab)

lemma kHighest_fwd {V : Type} [AddCommGroup V] [Module ℂ V] (hε : ε₁ = ε ∘ r) (ho : Ord ε₁ r)
    {E : Fin n → Fin n → Module.End ℂ V} {μ : Fin n → ℝ} {x : V} (h : KHighest ε₁ E μ x) :
    KHighest ε (fun a b => E (r.symm a) (r.symm b)) (μ ∘ r.symm) x := by
  refine ⟨fun a => h.1 _, fun a b hab he => h.2 _ _ (Ord.symm hε ho _ _ hab he) ?_⟩
  subst hε; simpa using he

lemma kHighest_bwd {V : Type} [AddCommGroup V] [Module ℂ V] (hε : ε₁ = ε ∘ r) (ho : Ord ε₁ r)
    {E : Fin n → Fin n → Module.End ℂ V} {μ : Fin n → ℝ} {x : V}
    (h : KHighest ε (fun a b => E (r.symm a) (r.symm b)) μ x) : KHighest ε₁ E (μ ∘ r) x := by
  subst hε
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · have := h.1 (r a)
    simpa using this
  · have := h.2 _ _ (ho _ _ hab he) he
    simpa using this

lemma kMod_ren (hε : ε₁ = ε ∘ r) (ho : Ord ε₁ r) (hτ : ∀ g, τ' g = τ (ren r g)) {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} (hK : IsKMod ε₁ τ D E) :
    IsKMod ε τ' D (fun a b => E (r.symm a) (r.symm b)) := by
  have hcomp : ∀ a b, ε₁ (r.symm a) = ε₁ (r.symm b) ↔ ε a = ε b := fun a b => by subst hε; simp
  refine ⟨fun v => ?_, fun X hX v => ?_, fun a b c d => ?_, fun a b x y => ?_, fun x => ?_,
    fun μ T hT => ?_, fun μ x hx hh => ?_⟩
  · rw [hK.mem]
    exact ⟨kfin_ren hε hτ, kfin_ren (hε_symm hε) (hτ_symm hτ)⟩
  · subst hε
    have h := hK.real (ren r X) (mem_inG r hX) v
    have e1 : (fun t : ℝ => τ' (NormedSpace.exp ((t : ℂ) • X)) (v : H)) =
        fun t : ℝ => τ (NormedSpace.exp ((t : ℂ) • ren r X)) (v : H) := by
      funext t
      rw [hτ, ← exp_ren]
      congr 3
    have e2 : (∑ a, ∑ b, X a b • ((E (r.symm a) (r.symm b) v : D) : H)) =
        ∑ a, ∑ b, (ren r X) a b • ((E a b v : D) : H) := by
      refine (Fintype.sum_equiv r.symm _ _ (fun a => ?_))
      refine (Fintype.sum_equiv r.symm _ _ (fun b => ?_))
      simp [ren]
    rw [e1, e2]
    exact h
  · have := hK.gl (r.symm a) (r.symm b) (r.symm c) (r.symm d)
    simpa using this
  · have := hK.unit (r.symm a) (r.symm b) x y
    have e : sgn ε₁ (r.symm a) (r.symm b) = sgn ε a b := by
      unfold sgn; simp only [hcomp]
    rwa [e] at this
  · obtain ⟨S, h1, h2, h3⟩ := hK.locFin x
    refine ⟨S, h1, fun a b he v hv => h2 _ _ ((hcomp a b).2 he) v hv, h3⟩
  · have hT' := kType_ren (hε_symm hε) (Ord.symm hε ho) (hτ_symm hτ) hT
    obtain ⟨v, hv, hvT, hvh⟩ := hK.hw _ T hT'
    refine ⟨v, hv, hvT, ?_⟩
    have := kHighest_fwd hε ho hvh
    convert this using 1
    ext a; simp
  · obtain ⟨T, hT⟩ := hK.ty _ x hx (kHighest_bwd hε ho hh)
    refine ⟨T, ?_⟩
    have := kType_ren hε ho hτ hT
    convert this using 1
    ext a; simp

end Rep

end GlobalTheory.CompanionTheory.RenumDS

namespace GlobalTheory.CompanionTheory.RenumDS

open MeasureTheory

variable {n : ℕ}

def unitsRen (r : Equiv.Perm (Fin n)) : (Matrix (Fin n) (Fin n) ℂ)ˣ ≃* (Matrix (Fin n) (Fin n) ℂ)ˣ :=
  Units.mapEquiv (Matrix.reindexAlgEquiv ℂ ℂ r.symm).toMulEquiv

lemma unitsRen_val (r : Equiv.Perm (Fin n)) (g : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    ((unitsRen r g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = ren r g := by
  ext i j; simp [unitsRen, ren]

lemma unitsRen_symm_val (r : Equiv.Perm (Fin n)) (g : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    (((unitsRen r).symm g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = ren r.symm g := by
  ext i j; simp [unitsRen, ren]

lemma continuous_unitsRen (r : Equiv.Perm (Fin n)) : Continuous (unitsRen r) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have : (Units.val ∘ unitsRen r) = ren r ∘ Units.val := by
      funext g; exact unitsRen_val r g
    rw [this]
    exact (continuous_ren r).comp Units.continuous_val
  · have : (fun g => (((unitsRen r g)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) =
        fun g : (Matrix (Fin n) (Fin n) ℂ)ˣ => ren r ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
      funext g; rw [← map_inv, unitsRen_val]
    rw [this]
    exact (continuous_ren r).comp (Units.continuous_val.comp continuous_inv)

lemma continuous_unitsRen_symm (r : Equiv.Perm (Fin n)) : Continuous (unitsRen r).symm := by
  have : ((unitsRen r).symm : _ → _) = unitsRen r.symm := by
    funext g; ext1; rw [unitsRen_symm_val, unitsRen_val]
  rw [this]
  exact continuous_unitsRen r.symm

def ujRen (ε : Fin n → Bool) (r : Equiv.Perm (Fin n)) : Formalism.REAL.UJ ε ≃* Formalism.REAL.UJ (ε ∘ r) where
  toFun g := ⟨unitsRen r g, by
    show Formalism.REAL.inUJ _ _
    rw [unitsRen_val]
    exact mem_UJ r (show _ ∈ PI.UpqRep.UJset ε from g.2)⟩
  invFun g := ⟨(unitsRen r).symm g, by
    show Formalism.REAL.inUJ _ _
    rw [unitsRen_symm_val]
    have h := mem_UJ r.symm (show _ ∈ PI.UpqRep.UJset (ε ∘ r) from g.2)
    have e : (ε ∘ r) ∘ r.symm = ε := by ext a; simp
    rw [e] at h
    exact h⟩
  left_inv g := by simp
  right_inv g := by simp
  map_mul' g h := by ext1; simp

lemma continuous_ujRen (ε : Fin n → Bool) (r : Equiv.Perm (Fin n)) : Continuous (ujRen ε r) :=
  Continuous.subtype_mk ((continuous_unitsRen r).comp continuous_subtype_val) _

lemma continuous_ujRen_symm (ε : Fin n → Bool) (r : Equiv.Perm (Fin n)) : Continuous (ujRen ε r).symm :=
  Continuous.subtype_mk ((continuous_unitsRen_symm r).comp continuous_subtype_val) _

lemma memLp_ren (ε : Fin n → Bool) (r : Equiv.Perm (Fin n)) {f : Formalism.REAL.UJ (ε ∘ r) → ℂ}
    (h : MemLp f 2 (Formalism.REAL.muG (ε ∘ r))) : MemLp (f ∘ ujRen ε r) 2 (Formalism.REAL.muG ε) := by
  let e := ujRen ε r
  have he := continuous_ujRen ε r
  have hes := continuous_ujRen_symm ε r
  let hm : Formalism.REAL.UJ ε ≃ₜ Formalism.REAL.UJ (ε ∘ r) := ⟨e.toEquiv, he, hes⟩
  haveI hH : (Measure.map e (Formalism.REAL.muG ε)).IsHaarMeasure := MulEquiv.isHaarMeasure_map (Formalism.REAL.muG ε) e he hes
  have hs := Measure.isMulLeftInvariant_eq_smul (Measure.map e (Formalism.REAL.muG ε)) (Formalism.REAL.muG (ε ∘ r))
  have h1 : MemLp f 2 (Measure.map e (Formalism.REAL.muG ε)) := by
    rw [hs, ENNReal.smul_def]
    exact h.smul_measure ENNReal.coe_ne_top
  exact (hm.measurableEmbedding.memLp_map_measure_iff).1 h1

section Rep

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ε ε₁ : Fin n → Bool} {r : Equiv.Perm (Fin n)} {τ τ' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

lemma sqIrr_ren (hε : ε₁ = ε ∘ r) (hτ : ∀ g, τ' g = τ (ren r g)) (h : GlobalTheory.Dec.IsSqIntIrr ε₁ τ) :
    GlobalTheory.Dec.IsSqIntIrr ε τ' := by
  subst hε
  obtain ⟨hc, hn, ⟨⟨h1, hm⟩, hi, hcont⟩, hirr, hsq⟩ := h
  have memU : ∀ {g}, g ∈ Formalism.MainNotions.S.UJset ε → ren r g ∈ Formalism.MainNotions.S.UJset (ε ∘ r) := fun {g} hg =>
    mem_UJ r (show g ∈ PI.UpqRep.UJset ε from hg)
  have memU' : ∀ {g}, g ∈ Formalism.MainNotions.S.UJset (ε ∘ r) → ren r.symm g ∈ Formalism.MainNotions.S.UJset ε := fun {g} hg => by
    have h := mem_UJ r.symm (show g ∈ PI.UpqRep.UJset (ε ∘ r) from hg)
    have e : (ε ∘ r) ∘ r.symm = ε := by ext a; simp
    rw [e] at h
    exact h
  refine ⟨hc, hn, ⟨⟨?_, fun a ha b hb => ?_⟩, fun g hg v => ?_, fun v => ?_⟩, fun S hS hst => ?_, fun v w => ?_⟩
  · rw [hτ, ren_one, h1]
  · rw [hτ, hτ, hτ, ren_mul, hm _ (memU ha) _ (memU hb)]
  · rw [hτ]; exact hi _ (memU hg) v
  · have : (fun g => τ' g v) = fun g => τ (ren r g) v := by funext g; rw [hτ]
    rw [this]
    exact (hcont v).comp (continuous_ren r).continuousOn (fun g hg => memU hg)
  · refine hirr S hS fun g hg v hv => ?_
    have := hst (ren r.symm g) (memU' hg) v hv
    rwa [hτ, ren_ren_symm] at this
  · have h2 := memLp_ren ε r (hsq v w)
    have : Formalism.MainNotions.S.coefOn (ε := ε) τ' v w = Formalism.MainNotions.S.coefOn (ε := ε ∘ r) τ v w ∘ ujRen ε r := by
      funext g
      show ⟪w, τ' _ v⟫_ℂ = ⟪w, τ _ v⟫_ℂ
      rw [hτ]
      congr 3
    rw [this]
    exact h2

end Rep

open Formalism.REAL (KHighest)
open CompanionTheory.D.LK (IsKMod)

theorem dsOfArr : CompanionTheory.RgExh.Fin.DSOfArr := by
  intro n ε s mu hl hord
  obtain ⟨H, i1, i2, σ0, hds⟩ := CompanionTheory.RgDs.B.dsExists n (ε ∘ s) mu hl
  have hC : CompleteSpace H := hds.1
  refine ⟨H, i1, i2, hC, fun g => σ0 (ren s g), ?_, fun D E hK => ?_⟩
  · exact sqIrr_ren rfl (fun g => rfl) ⟨hds.1, hds.2.1, hds.2.2.1, hds.2.2.2.1, hds.2.2.2.2.1⟩
  · have hε' : ε = (ε ∘ s) ∘ s.symm := by ext a; simp
    have ho : Ord ε s.symm := Ord.symm (ε₁ := ε ∘ s) (r := s) rfl hord
    have hK' : IsKMod (ε ∘ s) σ0 D (fun a b => E (s a) (s b)) :=
      kMod_ren (ε₁ := ε) (ε := ε ∘ s) (r := s.symm) (τ := fun g => σ0 (ren s g)) (τ' := σ0) hε' ho
        (fun g => by show σ0 g = σ0 (ren s (ren s.symm g)); rw [ren_ren_symm]) hK
    refine ⟨⟨hl, hord, fun μ x hx hh => ?_, ?_⟩, fun ν x hx hh => ?_⟩
    · obtain ⟨T, hT⟩ := hK'.ty μ x hx hh
      exact hds.2.2.2.2.2.2 μ T hT
    · obtain ⟨S, hS⟩ := hds.2.2.2.2.2.1
      obtain ⟨v, hv, -, hvh⟩ := hK'.hw _ S hS
      exact ⟨v, hv, hvh⟩
    · obtain ⟨T, hT⟩ := hK'.ty ν x hx hh
      exact CompanionTheory.RgDs.B.kTypesAbove n (ε ∘ s) mu H σ0 hl hds ν T hT

end GlobalTheory.CompanionTheory.RenumDS
