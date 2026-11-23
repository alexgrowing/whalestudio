import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumFixedAlmostAllPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyMemMaximalCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairLocalFinitePlacesProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairIntegralCompactInvariantStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section
namespace GlobalTheory.FinFactor

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {d : ℕ}
  {W : Spc F E d}

def Loc (v : Pl F) (A B : Matrix (Fin d) (Fin d) (AE F E)) : Prop := ∀ u : AF F, At (evFin F v) u → u • A = u • B

theorem Loc.mul {v : Pl F} {A A' B B' : Matrix (Fin d) (Fin d) (AE F E)} (hA : Loc v A A') (hB : Loc v B B') :
    Loc v (A * B) (A' * B') := by
  intro u hu
  rw [← Matrix.smul_mul, hA u hu, Matrix.smul_mul, ← Matrix.mul_smul, hB u hu, Matrix.mul_smul]

theorem Loc.trans {v : Pl F} {A B C : Matrix (Fin d) (Fin d) (AE F E)} (h1 : Loc v A B) (h2 : Loc v B C) : Loc v A C :=
  fun u hu => (h1 u hu).trans (h2 u hu)

theorem Loc.symm {v : Pl F} {A B : Matrix (Fin d) (Fin d) (AE F E)} (h1 : Loc v A B) : Loc v B A :=
  fun u hu => (h1 u hu).symm

theorem Loc.refl (v : Pl F) (A : Matrix (Fin d) (Fin d) (AE F E)) : Loc v A A := fun _ _ => rfl

theorem Loc.inv {v : Pl F} {g g' : UA σ W.J} (h : Loc v (mat g) (mat g')) : Loc v (mat g⁻¹) (mat g'⁻¹) := by
  have e1 : mat g⁻¹ = mat g⁻¹ * mat g' * mat g'⁻¹ := by
    rw [Matrix.mul_assoc, ← GlobalTheory.StabHaar.mat_mul g' g'⁻¹, mul_inv_cancel, GlobalTheory.StabHaar.mat_one, Matrix.mul_one]
  have e2 : mat g'⁻¹ = mat g⁻¹ * mat g * mat g'⁻¹ := by
    rw [← GlobalTheory.StabHaar.mat_mul g⁻¹ g, inv_mul_cancel, GlobalTheory.StabHaar.mat_one, Matrix.one_mul]
  have h' : Loc v (mat g⁻¹ * mat g' * mat g'⁻¹) (mat g⁻¹ * mat g * mat g'⁻¹) :=
    ((Loc.refl v (mat g⁻¹)).mul h.symm).mul (Loc.refl v _)
  intro u hu
  rw [e1, h' u hu, ← e2]

theorem loc_one_of_ne {v w : Pl F} (hwv : w ≠ v) {g : UA σ W.J} (hg : g ∈ UAt σ W (evFin F w)) : Loc v (mat g) 1 := by
  intro u hu
  have h := hg u (GlobalTheory.ThK.LocalOps.evFin_of_at hwv hu)
  rw [smul_sub, sub_eq_zero] at h
  exact h

theorem loc_listProd (h : Pl F → UA σ W.J) (v : Pl F) :
    ∀ l : List (Pl F), (∀ w ∈ l, h w ∈ UAt σ W (evFin F w)) →
      (v ∉ l → Loc v (mat (l.map h).prod) 1) ∧ (l.Nodup → v ∈ l → Loc v (mat (l.map h).prod) (mat (h v)))
  | [], _ => ⟨fun _ => by simp [GlobalTheory.StabHaar.mat_one]; exact fun _ _ => rfl, fun _ hv => absurd hv (by simp)⟩
  | a :: l, hl => by
    have ih := loc_listProd h v l fun w hw => hl w (List.mem_cons_of_mem a hw)
    have ha := hl a List.mem_cons_self
    simp only [List.map_cons, List.prod_cons, GlobalTheory.StabHaar.mat_mul]
    refine ⟨fun hv => ?_, fun hnd hv => ?_⟩
    · rw [List.mem_cons, not_or] at hv
      have := (loc_one_of_ne (Ne.symm hv.1) ha).mul (ih.1 hv.2)
      rwa [Matrix.one_mul] at this
    · rw [List.nodup_cons] at hnd
      by_cases hva : v = a
      · subst hva
        have := (Loc.refl v (mat (h v))).mul (ih.1 hnd.1)
        rwa [Matrix.mul_one] at this
      · have hv' : v ∈ l := (List.mem_cons.1 hv).resolve_left hva
        have := (loc_one_of_ne (Ne.symm hva) ha).mul (ih.2 hnd.2 hv')
        rwa [Matrix.one_mul] at this

theorem uAt_fin_of_uAt {v : Pl F} {g : UA σ W.J} (hg : g ∈ UAt σ W (evFin F v)) :
    g ∈ UAt σ W (fun u : AF F => u.2) := by
  intro u hu
  apply hg u
  change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (sndA F u) = 0
  have : sndA F u = u.2 := rfl
  rw [this]
  simp only at hu
  rw [hu, map_zero]

end GlobalTheory.FinFactor

open GlobalTheory.FinFactor in

theorem GlobalTheory.FinFactor.om_pure_factor : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ hf ∈ UAt σ W (fun u : AF F => u.2), ∀ h : Pl F → UA σ W.J,
      (∀ v, h v ∈ UAt σ W (evFin F v) ∧ ∀ u : AF F, At (evFin F v) u → u • mat (h v) = u • mat hf) →
      ∃ S : Finset (Pl F), ∀ T : Finset (Pl F), S ⊆ T → ∀ (f : SInf F (Fin n × Fin d))
        (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) → (∀ v ∉ T, φ v = M.vac v) →
        ∃ φ₁ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ,
          (∀ v, φ₁ v ∈ SB _ ∧ Acts (evFin F v) (om (1, h v)) (φ v) (φ₁ v)) ∧ (∀ v ∉ T, φ₁ v = M.vac v) ∧
          om (1, hf) (pure f φ) = pure f φ₁ := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP hf hhf h hh
  classical
  have hA := GlobalTheory.T.vacuum_fixed_almost_all_places hKP F E σ B n d X W M χX χW om r s r' s' hP
  have hB := GlobalTheory.T.eventually_mem_maximal_compact F E σ d W hP.skew.lat hf
  have hfin := Filter.eventually_cofinite.1 (hA.and hB)
  refine ⟨hfin.toFinset, fun T hST f φ hφ hφT => ?_⟩
  have good : ∀ v ∉ T, (∀ g ∈ GlobalTheory.InertSph.KAt σ W v, Acts (evFin F v) (om (1, g)) (M.vac v) (M.vac v)) ∧
      (∀ g ∈ UAt σ W (evFin F v), (∀ u : AF F, At (evFin F v) u → u • mat g = u • mat hf) →
        g ∈ GlobalTheory.InertSph.KAt σ W v) := by
    intro v hv
    have : v ∉ hfin.toFinset := fun h' => hv (hST h')
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at this
    exact this
  have h1X : ∀ v : Pl F, (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := fun v u _ => by
    show u • (mat (1 : UA σ X.J) - 1) = 0
    rw [GlobalTheory.StabHaar.mat_one, sub_self, smul_zero]
  choose ψ hψSB hψA using fun v (_ : v ∈ T) =>
    GlobalTheory.ThK.LocalOps.acts_exists hP v (1, h v) (h1X v) (hh v).1 (φ v) (hφ v)
  let φ₁ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ := fun v => if hv : v ∈ T then ψ v hv else M.vac v
  have hvacSB : ∀ v, M.vac v ∈ SB (Fin n × Fin d → Fv F v) := fun v => (hP.good.vac v).1
  have hout : ∀ v ∉ T, φ₁ v = M.vac v := fun v hv => by simp only [φ₁, dif_neg hv]
  have hloc : ∀ v, φ₁ v ∈ SB _ ∧ Acts (evFin F v) (om (1, h v)) (φ v) (φ₁ v) := by
    intro v
    by_cases hv : v ∈ T
    · simp only [φ₁, dif_pos hv]; exact ⟨hψSB v hv, hψA v hv⟩
    · rw [hout v hv, hφT v hv]
      exact ⟨hvacSB v, (good v hv).1 _ ((good v hv).2 _ (hh v).1 (hh v).2)⟩
  refine ⟨φ₁, hloc, hout, ?_⟩
  set l := T.toList with hl
  have hlU : ∀ w ∈ l, h w ∈ UAt σ W (evFin F w) := fun w _ => (hh w).1
  set P := (l.map h).prod with hPdef
  have hPU : P ∈ (GlobalTheory.ThK.UAtSub (F := F) (E := E) (R := Af F) σ W (fun u : AF F => u.2) : Subgroup (UA σ W.J)) := by
    refine Subgroup.list_prod_mem _ (l := l.map h) fun x hx => ?_
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
    exact uAt_fin_of_uAt (hh w).1
  have hfac : om (1, hf) = om (1, P) * om (1, P⁻¹ * hf) := by
    rw [← map_mul, Prod.mk_mul_mk, one_mul, mul_inv_cancel_left]
  have hk1 : P⁻¹ * hf ∈ UAt σ W (fun u : AF F => u.2) :=
    ((GlobalTheory.ThK.UAtSub (F := F) (E := E) (R := Af F) σ W (fun u : AF F => u.2) : Subgroup (UA σ W.J))).mul_mem ((GlobalTheory.ThK.UAtSub (F := F) (E := E) (R := Af F) σ W (fun u : AF F => u.2)).inv_mem hPU) hhf
  have hk2 : ∀ v ∈ T, ∀ u : AF F, At (evFin F v) u →
      u • mat (P⁻¹ * hf) = u • (1 : Matrix (Fin d) (Fin d) (AE F E)) := by
    intro v hv
    have hPv : Loc v (mat P) (mat hf) :=
      ((loc_listProd h v l hlU).2 (Finset.nodup_toList T) (Finset.mem_toList.2 hv)).trans (hh v).2
    have := (Loc.inv hPv).mul (Loc.refl v (mat hf))
    rw [← GlobalTheory.StabHaar.mat_mul, ← GlobalTheory.StabHaar.mat_mul, inv_mul_cancel, GlobalTheory.StabHaar.mat_one] at this
    exact this
  have hk3 : ∀ v ∉ T, ∀ g ∈ UAt σ W (evFin F v), (∀ u : AF F, At (evFin F v) u → u • mat g = u • mat (P⁻¹ * hf)) →
      Acts (evFin F v) (om (1, g)) (M.vac v) (M.vac v) := by
    intro v hv g hg hgk
    have hP1 : Loc v (mat P) (mat (1 : UA σ W.J)) := by
      rw [GlobalTheory.StabHaar.mat_one]; exact (loc_listProd h v l hlU).1 (fun h' => hv (Finset.mem_toList.1 h'))
    have := (Loc.inv hP1).mul (Loc.refl v (mat hf))
    rw [← GlobalTheory.StabHaar.mat_mul, ← GlobalTheory.StabHaar.mat_mul, inv_one, one_mul] at this
    exact (good v hv).1 _ ((good v hv).2 g hg ((show Loc v (mat g) (mat (P⁻¹ * hf)) from hgk).trans this))
  rw [hfac, Module.End.mul_apply,
    GlobalTheory.T.pair_integral_compact_invariant F E σ B n d X W M χX χW om r s r' s' hP T (P⁻¹ * hf) hk1 hk2 hk3 f φ hφ hφT]
  refine GlobalTheory.T.pair_local_finite_places_product F E σ B n d X W M χX χW om r s r' s' hP l (Finset.nodup_toList T) h hlU f φ φ₁ hφ
    (Filter.mem_of_superset T.finite_toSet.compl_mem_cofinite fun v hv => hφT v hv) (fun v hv => hloc v) (fun v hv => ?_)
  have hvT : v ∉ T := fun h' => hv (Finset.mem_toList.2 h')
  rw [hout v hvT, hφT v hvT]
