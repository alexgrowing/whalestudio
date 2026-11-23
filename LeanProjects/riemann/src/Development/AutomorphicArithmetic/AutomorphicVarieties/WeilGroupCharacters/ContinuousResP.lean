import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CongruenceNumberRankThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp

namespace UpperTheory.V.W

instance coefLocal {l : ℕ} [Fact l.Prime] (c : Coef l) : IsLocalRing ↥c.O := c.dvr.toIsLocalRing

abbrev Plc (F : Type) [Field F] : Type := HeightOneSpectrum (𝓞 F)

def GDet.IsTwist {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (β : G →* Aˣ) (D' : GDet n A G) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra A B] (y : MonoidAlgebra B G),
    D'.D B y = D.D B (MonoidAlgebra.lift B (MonoidAlgebra B G) G
      { toFun := fun g => MonoidAlgebra.single g (algebraMap A B (β g))
        map_one' := by simp [← MonoidAlgebra.one_def]
        map_mul' := fun g h => by simp [MonoidAlgebra.single_mul_single] } y)

private theorem totDisc_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    TotallyDisconnectedSpace (G ⧸ N) := by
  have hsep : TotallySeparatedSpace (G ⧸ N) := by
    rw [totallySeparatedSpace_iff_exists_isClopen]
    intro x y hxy
    induction x using QuotientGroup.induction_on with
    | _ a =>
    induction y using QuotientGroup.induction_on with
    | _ b =>
    have hcl : IsClosed ((fun g : G => b⁻¹ * g) ⁻¹' (N : Set G)) :=
      hN.preimage (continuous_const.mul continuous_id)
    have ha : a ∈ ((fun g : G => b⁻¹ * g) ⁻¹' (N : Set G))ᶜ := by
      intro h
      exact hxy (QuotientGroup.eq.2 h).symm
    obtain ⟨C, hC, haC, hCsub⟩ := compact_exists_isClopen_in_isOpen hcl.isOpen_compl ha
    refine ⟨QuotientGroup.mk '' C, ⟨?_, QuotientGroup.isOpenMap_coe _ hC.isOpen⟩, ⟨a, haC, rfl⟩, ?_⟩
    · rw [← (QuotientGroup.isQuotientMap_mk N).isClosed_preimage, QuotientGroup.preimage_image_mk_eq_mul]
      exact hN.mul_left_of_isCompact hC.isClosed.isCompact
    · rintro ⟨c, hc, hcb⟩
      exact hCsub hc (QuotientGroup.eq.1 hcb.symm)
  infer_instance

section LocAlg

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w)

abbrev Emb (l : ℕ) [Fact l.Prime] (w : Plc F) : Type := {j : w.adicCompletion F →+* Qbar l // Continuous j}

def IsWtPart (κ : Dec (F := F) A →* (Qbar l)ˣ) (wt : Emb l w → ℤ) (ph : Ine (F := F) A →* (Qbar l)ˣ) : Prop :=
  IsOpen (ph.ker : Set (Ine (F := F) A)) ∧
    ∀ a : Weil h →* (w.adicCompletion F)ˣ, GlobalTheory.LocLanglands.IsLocalArtin h a → ∀ σ : Ine (F := F) A,
      ((κ (Subgroup.inclusion (Weil_le_Dec h) (ineIncl h σ)) * ph σ : (Qbar l)ˣ) : Qbar l) =
        ∏ᶠ τ : Emb l w, τ.1 (a (ineIncl h σ) : w.adicCompletion F) ^ (-wt τ)

def IsLocAlg (κ : Dec (F := F) A →* (Qbar l)ˣ) (wt : Emb l w → ℤ) : Prop := ∃ ph, IsWtPart h κ wt ph

end LocAlg

variable (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]

abbrev Lp : Type := ↥(maximalRealSubfield L)

instance : IsAlgClosure (Lp L) Ω where
  isAlgClosed := IsAlgClosure.isAlgClosed L
  isAlgebraic := haveI : Algebra.IsAlgebraic L Ω := IsAlgClosure.isAlgebraic; Algebra.IsAlgebraic.trans (Lp L) L Ω

abbrev resP : G L Ω →* G (Lp L) Ω := AlgEquiv.restrictScalarsHom (Lp L)

structure HidaSetting where
  odd : l ≠ 2
  unr : ∀ (A : ValuationSubring Ω) (v : Plc (Lp L)), IsPlaceOver A v → Ine (F := Lp L) A ≤ (resP L Ω).range
  c : G (Lp L) Ω
  hc : ∃ j : Ω →+* ℂ, ∀ x, j (c x) = starRingEnd ℂ (j x)
  w : Plc (Lp L) → Plc L
  A : Plc (Lp L) → ValuationSubring Ω
  hw : ∀ v, IsPlaceOver (A v) (w v)
  hA : ∀ v, IsPlaceOver (A v) v
  St : Finset (Plc (Lp L))
  St_l : ∀ u ∈ St, ((l : ℕ) : 𝓞 (Lp L)) ∉ u.asIdeal
  v0 : Plc (Lp L)
  v0_St : v0 ∉ St
  p : ℕ
  p_prime : p.Prime
  p_odd : p ≠ 2
  p_ne : p ≠ l
  p_unr : ¬ (p : ℤ) ∣ discr L
  norm_v0_eq_one : normV v0 = p
  split : ∀ v, (((l : ℕ) : 𝓞 (Lp L)) ∈ v.asIdeal ∨ v ∈ St ∨ v = v0) → Dec (F := Lp L) (A v) ≤ (resP L Ω).range

variable {l L Ω}

namespace HidaSetting

variable (s : HidaSetting l L Ω)

def S : Set (Plc (Lp L)) := {v | ((l : ℕ) : 𝓞 (Lp L)) ∈ v.asIdeal ∨ v ∈ s.St ∨ v = s.v0}

variable (l L) in

abbrev _root_.UpperTheory.V.W.Vl : Type := {v : Plc (Lp L) // ((l : ℕ) : 𝓞 (Lp L)) ∈ v.asIdeal}

structure Lev where
  S' : Set (Plc (Lp L))
  fin : S'.Finite
  sub : s.S ⊆ S'
  split : ∀ v ∈ S', Dec (F := Lp L) (s.A v) ≤ (resP L Ω).range
  η : GS Ω S' →* ℤˣ
  hη : ∀ g, η (toGS Ω S' g) = 1 ↔ g ∈ (resP L Ω).range
  η_open : IsOpen (η.ker : Set (GS Ω S'))
  η_c : η (toGS Ω S' s.c) = -1
  ε : GS Ω S' →* ℤ_[l]ˣ
  hε : ε.comp (toGS Ω S') = cycZ (Lp L) Ω l
  ε_cont : Continuous ε

theorem c_sq : s.c * s.c = 1 := by
  obtain ⟨j, hj⟩ := s.hc
  ext x
  apply j.injective
  simp [hj]

namespace Lev

variable {s} (V : s.Lev)

def pr : G L Ω →* V.η.ker :=
  ((toGS Ω V.S').comp (resP L Ω)).codRestrict _ fun g => (V.hη _).2 ⟨g, rfl⟩

theorem pr_cont (h : Continuous (resP L Ω)) : Continuous V.pr := ((continuous_toGS Ω _).comp h).subtype_mk _

end Lev

end HidaSetting

theorem continuous_resP : Continuous (resP L Ω) := Af.continuous_restrictScalarsHom _ _ _

def HidaSetting.Lev.frame {s : HidaSetting l L Ω} (V : s.Lev) : GFrame l where
  Γ := GS Ω V.S'
  cpt := inferInstance
  tdisc := totDisc_quot _ (isClosed_NS Ω V.S')
  η := V.η
  η_open := V.η_open
  c := toGS Ω V.S' s.c
  c_sq := by rw [← map_mul, s.c_sq, map_one]
  η_c := V.η_c
  ε := V.ε
  ε_cont := V.ε_cont
  Vl := Vl l L
  finV := haveI : Finite (Vl l L) := (V.fin.subset fun v (hv : _ ∈ v.asIdeal) => V.sub (Or.inl hv)).to_subtype
    Fintype.ofFinite _
  Gv v := Dec (F := L) (s.A v)
  cv v := isCompact_iff_compactSpace.1 (isClosed_Dec (F := L) (s.A v)).isCompact
  φ v := V.pr.comp (Dec (F := L) (s.A v)).subtype
  φ_cont v := (V.pr_cont continuous_resP).comp continuous_subtype_val
  Iv v := (Ine (F := L) (s.A v)).subgroupOf (Dec (F := L) (s.A v))
  St := s.St
  Iu u := (Ine (F := L) (s.A u)).map V.pr
  D0 := (Dec (F := L) (s.A s.v0)).map V.pr
  I0 := (Ine (F := L) (s.A s.v0)).map V.pr

end UpperTheory.V.W
