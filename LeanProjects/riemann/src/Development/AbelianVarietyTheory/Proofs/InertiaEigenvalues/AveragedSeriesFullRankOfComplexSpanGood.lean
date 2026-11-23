import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.RankDescent

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

theorem charZero_frac (i : X.Tw) : CharZero (FractionRing (X.O i)) :=
  (RingHom.charZero_iff ((IsFractionRing.map (A := X.O0 i) (B := X.O i) (K := FractionRing (X.O0 i))
      (L := FractionRing (X.O i)) (X.O_inj i)).comp (X.emb0 i)).injective).1 inferInstance

theorem eG_eG (i : X.Tw) (j : ℕ) (b : Bool) (x : Y.Fm i j b) :
    Formalism.MainNotions.IntegralHeckeForms.eG Y i j b (Formalism.MainNotions.IntegralHeckeForms.eG Y i j b x) = Formalism.MainNotions.IntegralHeckeForms.eG Y i j b x := by
  have h := congrArg (MonoidAlgebra.lift (FractionRing (X.O i)) (Module.End (FractionRing (X.O i)) (Y.Fm i j b)) (G0g N)
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (Y.actG i j b))) (Y.eAlg_idem i b)
  rw [map_mul] at h
  exact LinearMap.congr_fun h x

theorem good_idempotent_fixes_mem_good_type_space (i : X.Tw) (j : ℕ) (b : Bool) {x : Y.Fm i j b} (hx : x ∈ V0 Y i j b) :
    Formalism.MainNotions.IntegralHeckeForms.eG Y i j b x = x := by
  obtain ⟨y, -, rfl⟩ := hx
  exact eG_eG Y i j b y

open Formalism.MainNotions.IntegralHeckeForms in

theorem AO_eq (i : X.Tw) (j : ℕ) (b : Bool) (x : Y.Fm i j b) :
    AO Y i j b x = ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i)) • eG Y i j b x := by
  show ((D.what₂.restRowsFiniteGroupCard : ℕ) : X.O i) • eG Y i j b x = _
  rw [← map_natCast (algebraMap (X.O i) (FractionRing (X.O i))), algebraMap_smul]

open Formalism.MainNotions.IntegralHeckeForms in

theorem thetaSeries_mem_goodTypeForms (E : ExpDat Y) (i : X.Tw) (j : ℕ) (b : Bool) (a : Y.Dat i j b) (ha : a ∈ E.Dat0 i j b) :
    Y.th i j b a ∈ Fm0 Y i j b := by
  simp only [Fm0, Submodule.mem_iInf, LinearMap.mem_ker]
  intro u
  have := E.theta_base_equivariant i j b a ha u
  simp [this]

open Formalism.MainNotions.IntegralHeckeForms in

theorem AO_Th_le (E : ExpDat Y) (i : X.Tw) (j : ℕ) (b : Bool) :
    ∀ x ∈ (Th Y i j b (SgJ Y E i j b)).map (AO Y i j b), x ∈ V0 Y i j b := by
  rintro _ ⟨y, hy, rfl⟩
  rw [AO_eq]
  refine Submodule.smul_mem _ _ ⟨y, ?_, rfl⟩
  refine (Submodule.span_le (p := (Fm0 Y i j b).restrictScalars (X.O i))).2 ?_ hy
  rintro _ ⟨a, ha, rfl⟩
  exact thetaSeries_mem_goodTypeForms Y E i j b a ha

open Formalism.MainNotions.IntegralHeckeForms in

theorem fullRk_of_le (E : ExpDat Y) (i : X.Tw) (j : ℕ) (b : Bool)
    (h : V0 Y i j b ≤ Submodule.span (FractionRing (X.O i)) (eG Y i j b '' (Y.th i j b '' E.Dat0 i j b))) :
    FullRk Y E i j b (SgJ Y E i j b) := by
  haveI := charZero_frac (X := X) i
  have hc : ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i)) ≠ 0 := Nat.cast_ne_zero.2 D.what₂.restRowsFiniteGroupCard_pos.ne'
  refine ⟨subset_rfl, AO_Th_le Y E i j b, le_antisymm (Submodule.span_le.2 (AO_Th_le Y E i j b)) (h.trans ?_)⟩
  refine Submodule.span_le.2 ?_
  rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
  have e1 : eG Y i j b (Y.th i j b a) = ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i))⁻¹ • AO Y i j b (Y.th i j b a) := by
    rw [AO_eq, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [SetLike.mem_coe, e1]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, Submodule.subset_span ⟨a, ha, rfl⟩, rfl⟩)

section Descent

variable {ρ : Setup X} {i : X.Tw} {j : Fin D.R.m} {b : Bool}

theorem rd_mem_span (rd : Rd ρ Y i j b) (S : Set (Y.Fm i ((j : ℕ) + 1) b)) {y : Y.Fm i ((j : ℕ) + 1) b}
    (hy : y ∈ Submodule.span (FractionRing (X.O i)) S) : rd y ∈ Submodule.span ℂ (rd '' S) := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x z _ _ hx hz => rw [map_add]; exact add_mem hx hz
  | smul c x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

theorem mem_span_of_faithful {rd : Rd ρ Y i j b} (hf : Faithful rd) (S : Set (Y.Fm i ((j : ℕ) + 1) b))
    {x : Y.Fm i ((j : ℕ) + 1) b} (hx : rd x ∈ Submodule.span ℂ (rd '' S)) :
    x ∈ Submodule.span (FractionRing (X.O i)) S := by
  set W := Submodule.span (FractionRing (X.O i)) S
  by_contra hxW
  let bW := Module.finBasis (FractionRing (X.O i)) W
  let v : Fin (Module.finrank (FractionRing (X.O i)) W) → Y.Fm i ((j : ℕ) + 1) b := fun k => (bW k : Y.Fm i ((j : ℕ) + 1) b)
  have hv : LinearIndependent (FractionRing (X.O i)) v := bW.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hspan : Submodule.span (FractionRing (X.O i)) (Set.range v) = W := by
    have := congrArg (Submodule.map W.subtype) bW.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at this
    exact this
  have hli : LinearIndependent (FractionRing (X.O i)) (Fin.cons x v : Fin _ → Y.Fm i ((j : ℕ) + 1) b) :=
    linearIndependent_fin_cons.2 ⟨hv, by rw [hspan]; exact hxW⟩
  have hC := hf _ _ hli
  have hC' : LinearIndependent ℂ (Fin.cons (rd x) (fun k => rd (v k)) : Fin _ → (GA D (Wc D j) → ℂ)) := by
    convert hC using 1
    funext k
    refine Fin.cases ?_ (fun k => ?_) k <;> simp
  refine (linearIndependent_fin_cons.1 hC').2 ?_
  refine Submodule.span_le.2 ?_ hx
  rintro _ ⟨s, hs, rfl⟩
  have hsW : s ∈ Submodule.span (FractionRing (X.O i)) (Set.range v) := by
    rw [hspan]; exact Submodule.subset_span hs
  have := rd_mem_span Y rd _ hsW
  rw [← Set.range_comp] at this
  exact this

end Descent

theorem fullRk_of_spanGood : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), Comparison₂ hρ rd → (∀ i j b, Faithful (rd i j b)) → ∀ (E : IntegralHeckeForms.XD D) (i : D.ntw.Tw), (∀ j b, RatBase (rd i j b)) → (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b a, a ∈ E.Dat0 i j b) → SpanGood rd i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, FullRk D.nexp E i j b (SgJ D.nexp E i j b) := by
  intro D ρ hρ rd T hF E i hR hall hS j hj b
  have hj' := Finset.mem_Icc.1 hj
  obtain ⟨j', rfl⟩ : ∃ j' : Fin D.R.m, j = (j' : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  refine fullRk_of_le D.nexp E i _ b ?_
  intro x hx
  have h1 : rd i j' b x ∈ Submodule.span ℂ (rd i j' b '' (D.nexp.th i _ b '' E.Dat0 i _ b)) := by
    refine Submodule.span_mono ?_ (hS j' b x hx)
    rintro _ ⟨s, h, P, hd, rfl⟩
    obtain ⟨d, -, hc, hp⟩ := (T i j' b).dat_onto s h P hd (hR j' b s h P hd)
    refine ⟨D.nexp.th i _ b d, ⟨d, hall _ hj b d, rfl⟩, ?_⟩
    rw [(T i j' b).th_eq d, hc, hp]
  have h2 := mem_span_of_faithful D.nexp (hF i j' b) _ h1
  rw [← good_idempotent_fixes_mem_good_type_space D.nexp i _ b hx]
  have h3 := Submodule.mem_map_of_mem (f := Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i ((j' : ℕ) + 1) b) h2
  rwa [Submodule.map_span] at h3

end GlobalTheory.RankDescent

end
