import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Formalism.LocalToGlobal.Divisibility.ColumnFamilyPlaceCharacterComap
import Formalism.LocalToGlobal.Divisibility.TiedLemmas
import Formalism.LocalToGlobal.IndefiniteReal.LiftGoodPartComplexEqRangeFamily
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OrZeroOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RestrictedCharacterDataValid
import Formalism.LocalToGlobal.IndefiniteReal.PackageFromPrimitiveStatements

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Mem.R3.Res

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Level

open Formalism.IndefR.CxPass Formalism.IndefR.CxPass.LevelOperators

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  {A3 : FamIn3 K G Pl0 I0 Ty T m} {X : CxData A3.fam3.amb3} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ}
  {P1 : Subgroup G} {ψ1 : P1 →* Kˣ} {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)}
  {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)} {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3} {s : ℕ}

theorem volume_le_of_trivial_first_pair (hok : A3.fam3.Ok3 s) (hK : X.KFormL) (hJ : X.JIsoL (cvOf3 A3 P0 ψ0 P1 ψ1))
    {gW : ∀ j, Representation ℂ G (X.W j)} (hU : LiftActionUnitary X gW) (hG : LiftGroupEquivariance A3 X gW) (j : Fin m) (t : T) :
    X.goodPartComplexPoints (cvOf3 A3 P0 ψ0 P1 ψ1) false j t ≤ X.goodPartComplexPoints (cvOf3 A3 ⊥ 1 P1 ψ1) false j t := by
  have H := lift_hypotheses_of_unitary hok hK (cvOf3 A3 P0 ψ0 P1 ψ1) (fun _ _ _ _ => rfl) hJ hU hG j t
  have e0 := lift_good_part_complex_eq_range_family H (cv := cvOf3 A3 P0 ψ0 P1 ψ1) (b := false) (ℓ := A3.fam3.F.lvlA P0 ψ0) rfl
  have e2 := lift_good_part_complex_eq_range_family H (cv := cvOf3 A3 ⊥ 1 P1 ψ1) (b := false) (ℓ := A3.fam3.F.lvlA ⊥ 1) rfl
  have e1 : goodAt (A3.fam3.F.lvlA ⊥ 1).X (A3.fam3.F.lvlA ⊥ 1).P (A3.fam3.F.lvlA ⊥ 1).ψ = idemOf A3.fam3.F.X :=
    goodAt_bot A3.fam3.F.X _
  rw [e1] at e2
  exact e0.le.trans ((H.range_le A3.fam3.F.X P0 ψ0⁻¹).trans e2.ge)

theorem exists_crd (hok : A3.fam3.Ok3 s) (hK : X.KFormL) (hJ : X.JIsoL (cvOf3 A3 ⊥ 1 P1 ψ1)) (hRZ : X.RatZ)
    {gW : ∀ j, Representation ℂ G (X.W j)} (hU : LiftActionUnitary X gW) (hG : LiftGroupEquivariance A3 X gW) (j : Fin m) (t : T) (w : X.W j)
    (hw : LinearMap.adjoint (X.θ' j t) w ∈ X.goodPartComplexPoints (cvOf3 A3 ⊥ 1 P1 ψ1) false j t) :
    ∃ c, lin (X.uL (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false j t) c = LinearMap.adjoint (X.θ' j t) w := by
  have hrat := lift_rationality_of_equivariance (Dc := Dc) (Sp := Sp) (Zsc := Zsc) hok hK hJ hRZ hU hG false j t
  have hu := hrat.ge (Submodule.mem_inf.2 ⟨⟨w, rfl⟩, hw⟩)
  refine (Submodule.span_le (p := LinearMap.range (lin (X.uL (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false j t)))).2 ?_ hu
  rintro _ ⟨x, rfl⟩
  exact ⟨cpt A3.fam3.base3.v0.embedding x, (X.jL_toL (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false j t x).symm⟩

theorem range_w0C_le (hok : A3.fam3.Ok3 s) (hK : X.KFormL) (hJ : X.JIsoL (cvOf3 A3 P0 ψ0 P1 ψ1)) (hRZ : X.RatZ)
    {gW : ∀ j, Representation ℂ G (X.W j)} (hU : LiftActionUnitary X gW) (hG : LiftGroupEquivariance A3 X gW)
    (hL0 : LevelTypeOfLifts A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gW false P0 ψ0)
    (hA : X.ThmAop false) (hW : X.PartsW false) (hp : ∀ j t p v, 0 < X.lam j t p v) (j : Fin m) (t : T) :
    LinearMap.range (X.w0C false j) ≤ LinearMap.range (X.tC (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false j t) := by
  have hup := upper_level_lift_at_lower_type hok hK hJ hU hG hL0 j t
  refine (hW j).2.ge.trans (iSup_le fun p w hw => ?_)
  obtain ⟨c, hc⟩ := exists_crd (Dc := Dc) (Sp := Sp) (Zsc := Zsc) hok hK (fun j t x y => hJ j t x y) hRZ hU hG j t w
    (volume_le_of_trivial_first_pair hok hK hJ hU hG j t (hup ⟨w, hw.2, rfl⟩))
  have hl : ((X.lam j t p A3.fam3.base3.v0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hp j t p _).ne'
  have h1 : X.tC (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false j t c = ((X.lam j t p A3.fam3.base3.v0 : ℝ) : ℂ) • w :=
    (X.tC_eq _ false j t c).trans ((congrArg (X.θ' j t) hc).trans (hA j t p w hw))
  refine ⟨((X.lam j t p A3.fam3.base3.v0 : ℝ) : ℂ)⁻¹ • c, (map_smul _ _ _).trans ?_⟩
  rw [h1, smul_smul, inv_mul_cancel₀ hl, one_smul]

end Level

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T T' : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {f : T' → T} {μ : T'} {R : RealDat3 D (A3.comap id (f μ)) Ks} (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T')
  (tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {P1 : Subgroup G} {ψ1 : P1 →* D.what₂.LLˣ}

set_option maxHeartbeats 2000000 in

theorem pHecke (h : R.PHecke (bare3 _ P0 ψ0 P1 ψ1)) : (dat3 f μ R mu tw).PHecke (bare3 _ P0 ψ0 P1 ψ1) := by
  obtain ⟨⟨hE, h1⟩, hW, h2⟩ := h
  exact ⟨⟨fun t => hE (f t), fun t => h1.intw (f t), h1.comm, h1.parts⟩,
    fun j t => hW j (f t), fun j t => h2.intw j (f t), h2.comm, h2.parts⟩

set_option maxHeartbeats 2000000 in

theorem liftOnto (h : R.PHecke (bare3 _ P0 ψ0 P1 ψ1))
    (ho : ∀ hW, HeckeIntertwiningLifts (A3.comap id (f μ)) (R.toCx3 (bare3 _ P0 ψ0 P1 ψ1)) hW →
      U2.OntoC (A3.comap id (f μ)) (R.toCx3 (bare3 _ P0 ψ0 P1 ψ1)) P0 ψ0 P1 ψ1 hW) :
    ∀ hW, HeckeIntertwiningLifts (A3.comap f μ) ((dat3 f μ R mu tw).toCx3 (bare3 _ P0 ψ0 P1 ψ1)) hW →
      U2.OntoC (A3.comap f μ) ((dat3 f μ R mu tw).toCx3 (bare3 _ P0 ψ0 P1 ψ1)) P0 ψ0 P1 ψ1 hW := by
  classical
  intro hW' h'
  obtain ⟨hW0, h0⟩ := h.2
  let hW : ∀ j t, ((A3.comap id (f μ)).liftI j t).OpIx → Module.End ℂ ((R.toCx3 (bare3 _ P0 ψ0 P1 ψ1)).W j) :=
    fun j => Function.update (hW0 j) (f μ) (hW' j μ)
  have e : ∀ j, hW j (f μ) = hW' j μ := fun j => Function.update_self _ _ _
  have hh : HeckeIntertwiningLifts (A3.comap id (f μ)) (R.toCx3 (bare3 _ P0 ψ0 P1 ψ1)) hW := by
    refine ⟨fun j t => ?_, fun j => ?_, fun j p => ?_⟩
    · by_cases ht : t = f μ
      · subst ht
        intro i u
        rw [e j]
        exact h'.intw j μ i u
      · have e' : hW j t = hW0 j t := Function.update_of_ne ht _ _
        rw [e']
        exact h0.intw j t
    · exact (e j).symm ▸ h'.comm j
    · exact (h'.parts j p).trans (congrArg (fun z => Formalism.L2.Col.eigSum z _) (e j).symm)
  intro j
  have := ho hW hh j
  exact (e j) ▸ this

set_option maxHeartbeats 2000000 in

theorem pLevW {s : ℕ} (hok : (A3.comap id (f μ)).fam3.Ok3 s) (hs : (A3.comap id (f μ)).fam3.TypesSep3)
    (hC : R.WeakCharacterisation (bare3 _ P0 ψ0 P1 ψ1)) (h : PrimRows3 R (bare3 _ P0 ψ0 P1 ψ1)) :
    (dat3 f μ R mu tw).PLevW (bare3 _ P0 ψ0 P1 ψ1) := by
  have hR := complex_data_conditions_base_level_of_primitive_links hok hs hC h
  intro j
  have h1 := range_w0C_le hok hR.kFormL hR.jIsoL hR.ratZ hR.gUnitL hR.gEquivL hR.lower_level_lift_type hR.thmAop hR.partsW h.posScal.2 j (f μ)
  have h2 := h.levW j
  apply le_antisymm
  · exact le_inf (h1.trans (le_iSup_of_le μ le_rfl)) (h2.le.trans inf_le_right)
  · refine le_trans (inf_le_inf_right _ (iSup_le fun t => ?_)) h2.ge
    exact le_iSup_of_le (f t) le_rfl

set_option maxHeartbeats 4000000 in

theorem primRows3 {s : ℕ} (hok : (A3.comap id (f μ)).fam3.Ok3 s) (hs : (A3.comap id (f μ)).fam3.TypesSep3)
    (hC : R.WeakCharacterisation (bare3 _ P0 ψ0 P1 ψ1)) (h : PrimRows3 R (bare3 _ P0 ψ0 P1 ψ1)) :
    PrimRows3 (dat3 f μ R mu tw) (bare3 _ P0 ψ0 P1 ψ1) where
  heckeR t := h.heckeR (f t)
  heckeL j t := h.heckeL j (f t)
  hecke := pHecke mu tw h.hecke
  gUnit := h.gUnit
  gEquiv := ⟨fun t => h.gEquiv.1 (f t), fun j t => h.gEquiv.2 j (f t)⟩
  block := ⟨fun t => h.block.1 (f t), fun j t => h.block.2 j (f t)⟩
  rowTest := by
    obtain ⟨N, ψ, h1, h2⟩ := h.rowTest
    exact ⟨N, ψ, h1, fun t => h2 (f t)⟩
  liftTest j := by
    obtain ⟨N, ψ, h1, h2⟩ := h.liftTest j
    exact ⟨N, ψ, h1, fun t => h2 (f t)⟩
  liftTestB j := by
    obtain ⟨N, ψ, h1, h2, h3⟩ := h.liftTestB j
    exact ⟨N, ψ, h1, fun t => h2 (f t), h3⟩
  liftOnto := liftOnto mu tw h.hecke h.liftOnto
  pos b := by
    cases b
    · exact h.pos false
    · exact h.pos true
  posScal := ⟨h.posScal.1, fun i t => h.posScal.2 i (f t)⟩
  levE := h.levE
  h2P := ⟨h.h2P.1, fun t => h.h2P.2 (f t)⟩
  thmB := pThmB mu tw h.thmB
  sumE := h.sumE
  unif := h.unif
  mLat := h.mLat
  levW := pLevW mu tw hok hs hC h
  thmA i t := h.thmA i (f t)
  sumW := h.sumW
  scalConj := h.scalConj
  dimParts := h.dimParts

set_option maxHeartbeats 2000000 in

theorem intersectionNumber_baseChange (hf : Function.Injective f) (hC : R.WeakCharacterisation (bare3 _ P0 ψ0 P1 ψ1)) (h : Holds R (bare3 _ P0 ψ0 P1 ψ1)) :
    Holds (dat3 f μ R mu tw) (bare3 _ P0 ψ0 P1 ψ1) where
  prim := primRows3 mu tw h.ok h.sep hC h.prim
  aux := ⟨exAt (A := A3.A) mu tw h.aux.ex, h.aux.conj, h.aux.levelW, h.aux.integral⟩
  ok := (A3.comap id (f μ)).fam3.comap_ok_of_injective h.ok hf μ
  sep := h.sep

end GlobalTheory.Mem.R3.Res

end
