import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameEquivApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MtRead
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.MtRead.Red

section General

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem ALint_eq : ReciprocityTheory.Aut.ALint L = Formalism.L2.Herm.intAf (maximalRealSubfield L) L := by
  apply le_antisymm
  · refine Subring.closure_le.2 ?_
    rintro z (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact Subring.subset_closure (Or.inl ⟨⟨(y : L), ⟨y, rfl⟩⟩, rfl⟩)
    · exact Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
  · refine Subring.closure_le.2 ?_
    rintro x (⟨⟨_, y, rfl⟩, rfl⟩ | ⟨⟨c, hc⟩, rfl⟩)
    · exact Subring.subset_closure (Or.inl ⟨y, rfl⟩)
    · exact Subring.subset_closure (Or.inr ⟨c, hc, rfl⟩)

theorem proj_tmul_one (s : ReciprocityTheory.Aut.SplitPlace L) (y : L) :
    s.proj (y ⊗ₜ[maximalRealSubfield L] (1 : ReciprocityTheory.Aut.AFplus L)) = s.i y := by
  simp [ReciprocityTheory.Aut.SplitPlace.proj, Algebra.TensorProduct.lift_tmul]

theorem proj_mem (s : ReciprocityTheory.Aut.SplitPlace L) {z : ReciprocityTheory.Aut.AL L} (hz : z ∈ ReciprocityTheory.Aut.ALint L) :
    s.proj z ∈ s.v.adicCompletionIntegers (maximalRealSubfield L) := by
  have hle : ReciprocityTheory.Aut.ALint L ≤ (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring.comap s.proj := by
    refine Subring.closure_le.2 ?_
    rintro x (⟨y, rfl⟩ | ⟨c, hc, rfl⟩)
    · show s.proj _ ∈ s.v.adicCompletionIntegers (maximalRealSubfield L)
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, proj_tmul_one]
      exact s.split_le_one y
    · show s.proj _ ∈ s.v.adicCompletionIntegers (maximalRealSubfield L)
      simp only [ReciprocityTheory.Aut.SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul,
        map_one, one_mul]
      exact hc s.v
  exact hle hz

theorem proj_lt_one (s : ReciprocityTheory.Aut.SplitPlace L) (z : Formalism.L2.Herm.intAf (maximalRealSubfield L) L)
    (hz : z ∈ Formalism.L2.DIV.idS (maximalRealSubfield L) s.w.asIdeal) :
    Valued.v (s.proj (z : ReciprocityTheory.Aut.AL L)) < 1 := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Formalism.L2.DIV.oToS_coe, proj_tmul_one]
    exact hy
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Subring.coe_add, map_add]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hx hy)
  | smul c x _ hx =>
    rw [smul_eq_mul, Subring.coe_mul, map_mul, map_mul]
    have hc : Valued.v (s.proj (c : ReciprocityTheory.Aut.AL L)) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (proj_mem s ((ALint_eq (L := L)).ge c.2))
    calc Valued.v (s.proj (c : ReciprocityTheory.Aut.AL L)) * Valued.v (s.proj (x : ReciprocityTheory.Aut.AL L))
        ≤ 1 * Valued.v (s.proj (x : ReciprocityTheory.Aut.AL L)) := by gcongr
      _ < 1 := by rwa [one_mul]

theorem resS_iff (s : ReciprocityTheory.Aut.SplitPlace L) (z : Formalism.L2.Herm.intAf (maximalRealSubfield L) L) (u : 𝓞 L) :
    Valued.v (s.i (u : L) - s.proj (z : ReciprocityTheory.Aut.AL L)) < 1 ↔
      Formalism.L2.DIV.resS (maximalRealSubfield L) s.w z = Ideal.Quotient.mk s.w.asIdeal u := by
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (Formalism.L2.DIV.resS (maximalRealSubfield L) s.w z)
  have e1 : Formalism.L2.DIV.cmpS (maximalRealSubfield L) s.w.asIdeal (Formalism.L2.DIV.resS (maximalRealSubfield L) s.w z) =
      Ideal.Quotient.mk (Formalism.L2.DIV.idS (maximalRealSubfield L) s.w.asIdeal) z :=
    (RingEquiv.ofBijective (Formalism.L2.DIV.cmpS (maximalRealSubfield L) s.w.asIdeal)
      (Formalism.L2.DIV.cmpS_bij (F := maximalRealSubfield L) s.w.asIdeal s.w.ne_bot)).apply_symm_apply _
  have e2 : Formalism.L2.DIV.cmpS (maximalRealSubfield L) s.w.asIdeal (Ideal.Quotient.mk s.w.asIdeal b) =
      Ideal.Quotient.mk (Formalism.L2.DIV.idS (maximalRealSubfield L) s.w.asIdeal) (Formalism.L2.DIV.oToS (maximalRealSubfield L) L b) :=
    Ideal.quotientMap_mk
  have hmem : z - Formalism.L2.DIV.oToS (maximalRealSubfield L) L b ∈ Formalism.L2.DIV.idS (maximalRealSubfield L) s.w.asIdeal := by
    refine Ideal.Quotient.eq.1 ?_
    exact e1.symm.trans ((congrArg (Formalism.L2.DIV.cmpS (maximalRealSubfield L) s.w.asIdeal) hb.symm).trans e2)
  have h1 : Valued.v (s.proj (z : ReciprocityTheory.Aut.AL L) - s.i (algebraMap (𝓞 L) L b)) < 1 := by
    have := proj_lt_one s _ hmem
    rwa [AddSubgroupClass.coe_sub, map_sub, Formalism.L2.DIV.oToS_coe, proj_tmul_one] at this
  rw [← hb, eq_comm (a := Ideal.Quotient.mk s.w.asIdeal b), Ideal.Quotient.eq]
  show _ ↔ Valued.v (s.i ((u - b : 𝓞 L) : L)) < 1
  have e : s.i ((u - b : 𝓞 L) : L) =
      (s.i (u : L) - s.proj (z : ReciprocityTheory.Aut.AL L)) + (s.proj (z : ReciprocityTheory.Aut.AL L) - s.i (algebraMap (𝓞 L) L b)) := by
    simp only [RingOfIntegers.coe_eq_algebraMap, map_sub]
    ring
  constructor
  · intro h
    rw [e]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt h h1)
  · intro h
    rw [← sub_eq_iff_eq_add] at e
    rw [← e]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h h1)

def castE {F : Subfield L} (h : F = maximalRealSubfield L) :
    ReciprocityTheory.Aut.AL L ≃+* L ⊗[F] FiniteAdeleRing (𝓞 F) F :=
  (GlobalTheory.Mem.R3.swapCast h).symm.trans (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) L).toRingEquiv

theorem castE_rfl (x : ReciprocityTheory.Aut.AL L) : castE (L := L) rfl x = x :=
  (Algebra.TensorProduct.comm (maximalRealSubfield L) (ReciprocityTheory.Aut.AFplus L) L).apply_symm_apply x

theorem castE_mem_iff {F : Subfield L} (h : F = maximalRealSubfield L) (x : ReciprocityTheory.Aut.AL L) :
    castE h x ∈ Formalism.L2.Herm.intAf F L ↔ x ∈ ReciprocityTheory.Aut.ALint L := by
  subst h
  rw [castE_rfl, ALint_eq]

theorem resS_castE_iff {F : Subfield L} (h : F = maximalRealSubfield L) (s : ReciprocityTheory.Aut.SplitPlace L) (x : ReciprocityTheory.Aut.AL L)
    (z : Formalism.L2.Herm.intAf F L) (hz : (z : L ⊗[F] FiniteAdeleRing (𝓞 F) F) = castE h x) (u : 𝓞 L) :
    Valued.v (s.i (u : L) - s.proj x) < 1 ↔ Formalism.L2.DIV.resS F s.w z = Ideal.Quotient.mk s.w.asIdeal u := by
  subst h
  rw [castE_rfl] at hz
  rw [← hz]
  exact resS_iff s z u

end General

section Stab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m : ℕ}

theorem frGL_one_val (y : GL (Fin m) (Formalism.L2.Herm.intAf F E)) (a c : Fin m) :
    (frGL (1 : GL (Fin m) (E ⊗[F] Formalism.L2.Herm.Af F)) y).val a c = (y.val a c : E ⊗[F] Formalism.L2.Herm.Af F) := by
  have h : frGL (1 : GL (Fin m) (E ⊗[F] Formalism.L2.Herm.Af F)) y = intGL F E m y := by
    simp [frGL]
  rw [h]
  rfl

theorem mem_St_one (g : GL (Fin m) (E ⊗[F] Formalism.L2.Herm.Af F)) (h : ∀ a c, g.val a c ∈ Formalism.L2.Herm.intAf F E)
    (h' : ∀ a c, (g⁻¹).val a c ∈ Formalism.L2.Herm.intAf F E) : g ∈ St (1 : GL (Fin m) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
  have inj : Function.Injective ((Formalism.L2.Herm.intAf F E).subtype.mapMatrix (m := Fin m)) :=
    fun x y hxy => Matrix.ext fun a c => Subtype.ext (congrFun (congrFun hxy a) c)
  refine ⟨⟨Matrix.of fun a c => ⟨_, h a c⟩, Matrix.of fun a c => ⟨_, h' a c⟩, inj ?_, inj ?_⟩, ?_⟩
  · rw [map_mul, map_one]
    exact g.mul_inv
  · rw [map_mul, map_one]
    exact g.inv_mul
  · refine Units.ext (Matrix.ext fun a c => ?_)
    rw [frGL_one_val]
    rfl

end Stab

theorem red_eq_local : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n), IdFrame hF P → ∀ (hn : V.rank = n) (κ : GAf D.host.E n), (κ ∈ ReciprocityTheory.Aut.Umax D.host.E n ↔ Lev.finE V (P.ψ κ) ∈ St (1 : GL (Fin V.rank) (Lev.EAf D))) ∧ ∀ s : ReciprocityTheory.Aut.SplitPlace D.host.E, κ ∈ ReciprocityTheory.Aut.Umax D.host.E n → ∀ a c : Fin V.rank, NX.locM s κ (Fin.cast hn a) (Fin.cast hn c) ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) ∧ ∀ u : 𝓞 D.host.E, Valued.v (s.i (u : D.host.E) - NX.locM s κ (Fin.cast hn a) (Fin.cast hn c)) < 1 ↔ (redFn (1 : GL (Fin V.rank) (Lev.EAf D)) s.w (Lev.finE V (P.ψ κ))).val a c = Ideal.Quotient.mk s.w.asIdeal u := by
  intro D V n hF P hP hn κ
  obtain ⟨hn', hP⟩ := hP
  have ent : ∀ (κ : GAf D.host.E n) a c, (Lev.finE V (P.ψ κ)).val a c =
      castE hF ((κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)) (Fin.cast hn a) (Fin.cast hn c)) := fun κ a c =>
    congrArg (Lev.swapAE D) (hP κ a c)
  have toSt : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n → Lev.finE V (P.ψ κ) ∈ St (1 : GL (Fin V.rank) (Lev.EAf D)) := fun hκ => by
    refine mem_St_one _ (fun a c => ?_) (fun a c => ?_)
    · rw [ent]
      exact (castE_mem_iff hF _).2 (hκ _ _)
    · rw [← map_inv, ← map_inv, ent]
      exact (castE_mem_iff hF _).2 (Subgroup.inv_mem _ hκ _ _)
  refine ⟨⟨toSt, ?_⟩, fun s hκ a c => ⟨proj_mem s (hκ _ _), fun u => ?_⟩⟩
  · rintro ⟨y, hy⟩ i j
    have h1 := ent κ (Fin.cast hn.symm i) (Fin.cast hn.symm j)
    rw [← hy, frGL_one_val] at h1
    exact (castE_mem_iff hF _).1 (h1 ▸ (y.val _ _).2)
  · obtain ⟨y, hy⟩ := toSt hκ
    have h1 := ent κ a c
    rw [← hy, frGL_one_val] at h1
    rw [← hy, redFn_frGL]
    exact resS_castE_iff hF s _ (y.val a c) h1 u

end GlobalTheory.MtRead.Red

end
