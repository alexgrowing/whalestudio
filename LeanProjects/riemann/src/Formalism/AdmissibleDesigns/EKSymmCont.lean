import Formalism.AdmissibleDesigns.FiniteClassesContinuousLattice
import Formalism.AdmissibleDesigns.ExistsWildInertiaCyclotomicGenerator
import Formalism.AdmissibleDesigns.CoboundaryMemFiniteClasses
import Formalism.AdmissibleDesigns.FgTopContinuousLinearMap
import ReciprocityTheory.ReductiveGroups.TraceFormulas.GlobAlgGoodO

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

set_option linter.style.haveILetI false

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KOrb

open Module Formalism.MainNotions.N.KHf Formalism.NG

section Gen

variable {O : Type} [CommRing O] [IsDomain O] [TopologicalSpace O]
  {LL : Type} [Field LL] [TopologicalSpace LL] (e : FractionRing O ≃+* LL)

abbrev modO (V : Type) [AddCommGroup V] [Module (FractionRing O) V] : Module O (TrV e V) :=
  Module.compHom (TrV e V) (e.toRingHom.comp (algebraMap O (FractionRing O)))

theorem contSMulO (hO : Continuous fun c : O => e (algebraMap O (FractionRing O) c)) (V : Type)
    [AddCommGroup V] [Module (FractionRing O) V] :
    letI := modO e V
    ContinuousSMul O (TrV e V) := by
  letI := modO e V
  exact ⟨(ModuleTopology.continuousSMul LL (TrV e V)).continuous_smul.comp
    ((hO.comp continuous_fst).prodMk continuous_snd)⟩

variable {A : Type} [Ring A] [Algebra O A]
  {V : Type} [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]
  [Module A V]

def smulL (hP : ∀ (c : O) (v : V), (algebraMap O A c) • v = c • v) (v : V) :
    letI := modO e V
    A →ₗ[O] TrV e V :=
  letI := modO e V
  { toFun := fun a => (a • v : V)
    map_add' := fun a b => add_smul a b v
    map_smul' := fun c a => by
      show (c • a) • v = e.symm (e (algebraMap O (FractionRing O) c)) • (a • v : V)
      rw [RingEquiv.symm_apply_apply, algebraMap_smul, Algebra.smul_def, mul_smul, hP] }

theorem smul_cont [TopologicalSpace A] [IsModuleTopology O A]
    (hO : Continuous fun c : O => e (algebraMap O (FractionRing O) c))
    (hP : ∀ (c : O) (v : V), (algebraMap O A c) • v = c • v) (v : V) :
    Continuous fun a : A => (show TrV e V from (a • v : V)) := by
  letI := modO e V
  haveI := contSMulO e hO V
  haveI : ContinuousAdd (TrV e V) := ModuleTopology.continuousAdd LL (TrV e V)
  exact (IsModuleTopology.continuous_of_linearMap (R := O) (smulL e hP v) :)

theorem orbit_cont {G Γ : Type} [Group G] [TopologicalSpace G] [Group Γ] [TopologicalSpace Γ]
    (ι : G →* Γ) (hι : Continuous ι) [TopologicalSpace A] [IsModuleTopology O A]
    (u : Γ → A) (hu : Continuous u) (ρ : Representation O Γ V) (hρ : ∀ g v, ρ g v = u g • v)
    (hO : Continuous fun c : O => e (algebraMap O (FractionRing O) c))
    (hP : ∀ (c : O) (v : V), (algebraMap O A c) • v = c • v) (v : TrV e V) :
    Continuous fun g => repL e ρ ι g v := by
  refine ((smul_cont e hO hP v).comp (hu.comp hι)).congr fun g => ?_
  show u (ι g) • (show V from v) = ρ (ι g) v
  exact (hρ _ _).symm

end Gen

section Rec

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

theorem eK_alg_cont {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    Continuous fun c : D.nd.O i => eK (D.nbr i w hw) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) c) := by
  have h : (fun c : D.nd.O i => eK (D.nbr i w hw) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) c)) =
      fun c => algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw)) ((D.nbr i w hw).eO c) :=
    funext fun c => by rw [eK_apply, Br.toLLK_alg]
  rw [h]
  exact continuous_subtype_val.comp (D.nbr i w hw).eO_cont

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (g0 : GE D.nd)
  (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

theorem uElt_cont_n
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (n : ℕ) :
    letI := K.Topo.rTopology (D.nd.O i) Dd.R'
    Continuous fun g : ↥(Γn i dc n) => uElt Dd.r Dd.χ (g : GE D.nd) := by
  letI := K.Topo.rTopology (D.nd.O i) Dd.R'
  exact (K.Topo.uElt_cont (hD := hD) (hc := hc)).comp continuous_subtype_val

theorem orbC_uRep
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)
    {V : Type} [AddCommGroup V] [Module Dd.R' V] [Module (D.nd.O i) V] [Module (FractionRing (D.nd.O i)) V]
    [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) V] [SMulCommClass Dd.R' (D.nd.O i) V]
    (hP : ∀ (c : D.nd.O i) (v : V), (algebraMap (D.nd.O i) Dd.R' c) • v = c • v) (n : ℕ) :
    OrbC i dc (resRep (uRep (D.nd.O i) (M := V) Dd.r Dd.χ) (Γn i dc n)) := by
  intro hn v
  letI := K.Topo.rTopology (D.nd.O i) Dd.R'
  haveI : IsModuleTopology (D.nd.O i) Dd.R' := K.Topo.rTop_isModuleTopology (D.nd.O i) Dd.R'
  have hι : Continuous (Br.iota D.nbr i _ hn) := (D.nbr i _ hn).e_symm_cont.congr fun g => rfl
  exact orbit_cont (eK (D.nbr i _ hn)) (Br.iota D.nbr i _ hn) hι
    (fun g : ↥(Γn i dc n) => uElt Dd.r Dd.χ (g : GE D.nd)) (uElt_cont_n i dc r π g0 eB e₁ s Dd hD hc n)
    _ (fun g v => rfl) (eK_alg_cont i _) hP v

theorem orbC_repE
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (x' : Dd.X') (n : ℕ) :
    letI := evalModO i (R' := Dd.R') x'
    haveI := evalTower i (R' := Dd.R') x'
    OrbC i dc (repE i dc Dd.r Dd.χ x' n) := by
  letI := evalModO i (R' := Dd.R') x'
  haveI := evalTower i (R' := Dd.R') x'
  haveI := evalComm i (R' := Dd.R') x'
  haveI := smulComm_O i (A := Dd.R') (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x')
  exact orbC_uRep i dc r π g0 eB e₁ s Dd hD hc (fun c v => evalScalar i x' c v) n

theorem latM_alg {n : Type} [Fintype n] [DecidableEq n] (ρ : Dd.R' →ₐ[D.nd.O i] Matrix n n (D.nd.O i))
    (c : D.nd.O i) (v : Formalism.RepresentationBoundsCohomology.SF.LatM (D.nd.O i) (FractionRing (D.nd.O i)) n ρ.toRingHom) :
    (algebraMap (D.nd.O i) Dd.R' c) • v = c • v := by
  funext j
  show ∑ k, (ρ (algebraMap (D.nd.O i) Dd.R' c)) j k • v k = c • v j
  rw [AlgHom.commutes]
  simp [Matrix.algebraMap_matrix_apply, Finset.sum_ite_eq, ite_smul]

end Rec

section Homeo

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem iotaHomeo : KBKa.IotaHomeo (Br.iota D.nbr i w hw) := by
  exact ⟨{ toEquiv := (D.nbr i w hw).e.symm.toEquiv, continuous_toFun := (D.nbr i w hw).e_symm_cont, continuous_invFun := (D.nbr i w hw).e_cont }, fun g => rfl⟩

theorem eK_cont :
    letI := K.Topo.fracTopology (D.nd.O i)
    Continuous (eK (D.nbr i w hw)) := by
  letI := K.Topo.fracTopology (D.nd.O i)
  haveI := K.Topo.fracTop_addGroup_O (D := D) i
  have hemb := (K.Topo.fracTop_O (D := D) i).1
  refine continuous_of_continuousAt_zero (eK (D.nbr i w hw)).toAddMonoidHom ?_
  show ContinuousAt (eK (D.nbr i w hw)) 0
  rw [← map_zero (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))), ← hemb.continuousAt_iff]
  exact (eK_alg_cont i hw).continuousAt

theorem eK_symm_val (z : Br.Ow (D.nbr i w hw)) :
    (eK (D.nbr i w hw)).symm (z : Br.LLw (D.nbr i w hw)) =
      algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) ((D.nbr i w hw).eO.symm z) := by
  rw [RingEquiv.symm_apply_eq, eK_apply, Br.toLLK_alg, RingEquiv.apply_symm_apply]
  rfl

theorem eK_symm_cont :
    letI := K.Topo.fracTopology (D.nd.O i)
    Continuous (eK (D.nbr i w hw)).symm := by
  letI := K.Topo.fracTopology (D.nd.O i)
  haveI := K.Topo.fracTop_addGroup_O (D := D) i
  have hemb := (K.Topo.fracTop_O (D := D) i).1
  have hOemb : Topology.IsOpenEmbedding
      (algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw))) :=
    ⟨Topology.IsEmbedding.subtypeVal, ReciprocityTheory.ChartRestriction.T2.GlobAlg.isOpen_range_OL (D.nbr i w hw).LL⟩
  refine continuous_of_continuousAt_zero (eK (D.nbr i w hw)).symm.toAddMonoidHom ?_
  show ContinuousAt (eK (D.nbr i w hw)).symm 0
  rw [← map_zero (algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw))), ← hOemb.continuousAt_iff]
  have hfun : ((eK (D.nbr i w hw)).symm ∘ algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw))) =
      fun z => algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) ((D.nbr i w hw).eO.symm z) :=
    funext fun z => eK_symm_val i hw z
  rw [hfun]
  exact (hemb.continuous.comp (D.nbr i w hw).eO_symm_cont).continuousAt

theorem homeoK :
    letI := K.Topo.fracTopology (D.nd.O i)
    KBKa.HomeoK (eK (D.nbr i w hw)) := by
  exact ⟨eK_cont i hw, eK_symm_cont i hw⟩

theorem topMatch_pi (n : Type) [Finite n] :
    letI := K.Topo.fracTopology (D.nd.O i)
    KBKa.TopMatch (eK (D.nbr i w hw)) (n → FractionRing (D.nd.O i)) := by
  letI := K.Topo.fracTopology (D.nd.O i)
  haveI := K.Topo.fracTop_addGroup_O (D := D) i
  letI τ : TopologicalSpace (TrV (eK (D.nbr i w hw)) (n → FractionRing (D.nd.O i))) :=
    (Pi.topologicalSpace : TopologicalSpace (n → FractionRing (D.nd.O i)))
  let φ : (n → Br.LLw (D.nbr i w hw)) ≃L[Br.LLw (D.nbr i w hw)]
      TrV (eK (D.nbr i w hw)) (n → FractionRing (D.nd.O i)) :=
    { toFun := fun v j => (eK (D.nbr i w hw)).symm (v j)
      invFun := fun x j => eK (D.nbr i w hw) (x j)
      left_inv := fun v => funext fun j => (eK (D.nbr i w hw)).apply_symm_apply (v j)
      right_inv := fun x => funext fun j => (eK (D.nbr i w hw)).symm_apply_apply (x j)
      map_add' := fun v v' => funext fun j => map_add (eK (D.nbr i w hw)).symm (v j) (v' j)
      map_smul' := fun c v => funext fun j => map_mul (eK (D.nbr i w hw)).symm c (v j)
      continuous_toFun := continuous_pi fun j => (eK_symm_cont i hw).comp (continuous_apply j)
      continuous_invFun := continuous_pi fun j => (eK_cont i hw).comp (continuous_apply j) }
  have hM : IsModuleTopology (Br.LLw (D.nbr i w hw)) (TrV (eK (D.nbr i w hw)) (n → FractionRing (D.nd.O i))) :=
    IsModuleTopology.iso φ
  exact hM.1.symm

end Homeo

section Cyc

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

theorem prim_pow_eq {F : Type} [Field F] {z : F} {k a b : ℕ} (hk : k ≠ 0) (hz : IsPrimitiveRoot z k)
    (h : z ^ a = z ^ b) : ∃ q : ℤ, (b : ℤ) - a = k * q := by
  have hz0 : z ≠ 0 := hz.ne_zero hk
  have h1 : z ^ ((b : ℤ) - (a : ℤ)) = 1 := by
    rw [zpow_sub₀ hz0, zpow_natCast, zpow_natCast, h, div_self (pow_ne_zero _ hz0)]
  obtain ⟨q, hq⟩ := (hz.zpow_eq_one_iff_dvd _).1 h1
  exact ⟨q, hq⟩

variable {D : D7} (i : D.nd.Loc) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem eps_eq_chiQ (g : Br.G D.nbr i w hw) :
    ((eK (D.nbr i w hw) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
      ((epsU D.nd i ((Br.iota D.nbr i w hw g : _) : GE D.nd) : (D.nd.O i)ˣ) : D.nd.O i)) :
        Br.LLw (D.nbr i w hw)) : Formalism.BasicNotions.Loc.Om (D.nd.l i)) =
      algebraMap ℚ_[D.nd.l i] (Formalism.BasicNotions.Loc.Om (D.nd.l i))
        (((D.loc (D.nd.l i)).χQ (g : Formalism.BasicNotions.Loc.GQ (D.nd.l i)) : ℚ_[D.nd.l i]ˣ) : ℚ_[D.nd.l i]) := by
  have hp : (D.nd.l i).Prime := Fact.out
  let ψ : D.nd.O i →+* Formalism.BasicNotions.Loc.Om (D.nd.l i) :=
    ((D.nbr i w hw).LL.1.val.toRingHom).comp
      (((Formalism.BasicNotions.Loc.OL (D.nbr i w hw).LL).val.toRingHom).comp (D.nbr i w hw).eO.toRingHom)
  have hψ1 : ∀ c : D.nd.O i, ‖ψ c‖ ≤ 1 := fun c =>
    (ReciprocityTheory.ChartRestriction.T2.GlobAlg.mem_OL (D.nbr i w hw).LL _).1 ((D.nbr i w hw).eO c).2
  have hL : ∀ c : D.nd.O i, ((eK (D.nbr i w hw) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) c) :
      Br.LLw (D.nbr i w hw)) : Formalism.BasicNotions.Loc.Om (D.nd.l i)) = ψ c := by
    intro c
    rw [eK_apply, Br.toLLK_alg]
    rfl
  rw [hL]
  set h : GE D.nd := ((Br.iota D.nbr i w hw g : _) : GE D.nd) with hh
  set X : ℚ_[D.nd.l i] := (((D.loc (D.nd.l i)).χQ (g : Formalism.BasicNotions.Loc.GQ (D.nd.l i)) : ℚ_[D.nd.l i]ˣ) : ℚ_[D.nd.l i]) with hX
  set y0 : D.nd.O i := ((epsU D.nd i h : (D.nd.O i)ˣ) : D.nd.O i) with hy0
  have hl : ‖((D.nd.l i : ℕ) : Formalism.BasicNotions.Loc.Om (D.nd.l i))‖ = ((D.nd.l i : ℕ) : ℝ)⁻¹ := by
    have h1 := PadicAlgCl.norm_extends (D.nd.l i) ((D.nd.l i : ℕ) : ℚ_[D.nd.l i])
    rw [Padic.norm_p, map_natCast] at h1
    exact h1
  have hint : ∀ q : ℤ, ‖((q : ℤ) : Formalism.BasicNotions.Loc.Om (D.nd.l i))‖ ≤ 1 := by
    intro q
    have h1 := PadicAlgCl.norm_extends (D.nd.l i) ((q : ℤ) : ℚ_[D.nd.l i])
    rw [map_intCast] at h1
    rw [h1]
    exact Padic.norm_int_le_one q
  have key : ∀ m : ℕ, ‖ψ y0 - algebraMap ℚ_[D.nd.l i] (Formalism.BasicNotions.Loc.Om (D.nd.l i)) X‖ ≤
      (((D.nd.l i : ℕ) : ℝ)⁻¹) ^ m := by
    intro m
    haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
    haveI : CharZero D.nd.Om := charZero_of_injective_algebraMap (algebraMap D.host.E D.nd.Om).injective
    have hk : D.nd.l i ^ m ≠ 0 := pow_ne_zero _ hp.ne_zero
    haveI : NeZero (D.nd.l i ^ m) := ⟨hk⟩
    haveI : NeZero ((D.nd.l i ^ m : ℕ) : D.nd.Om) := ⟨Nat.cast_ne_zero.2 hk⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot D.nd.Om (D.nd.l i ^ m)
    obtain ⟨a, hga, hamod⟩ := K.Topo.isCyc_eps i h m ζ hζ.pow_eq_one
    obtain ⟨b, hXb, hgb⟩ := (D.loc (D.nd.l i)).χQ_cyc (g : Formalism.BasicNotions.Loc.GQ (D.nd.l i)) m ((D.nbr i w hw).j ζ)
      (by rw [← map_pow, hζ.pow_eq_one, map_one])
    have hcomm := (D.nbr i w hw).e_comm (Br.iota D.nbr i w hw g) ζ
    have hei : (D.nbr i w hw).e (Br.iota D.nbr i w hw g) = g := MulEquiv.apply_symm_apply _ g
    rw [hei] at hcomm
    have hab : ((D.nbr i w hw).j ζ) ^ a = ((D.nbr i w hw).j ζ) ^ b := by
      rw [← hgb, hcomm, ← map_pow]
      congr 1
      exact hga.symm
    obtain ⟨q, hq⟩ := prim_pow_eq hk (hζ.map_of_injective (D.nbr i w hw).j.injective) hab
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hamod
    have hy0' : ψ y0 = (a : Formalism.BasicNotions.Loc.Om (D.nd.l i)) + ψ y * ((D.nd.l i : ℕ) : Formalism.BasicNotions.Loc.Om (D.nd.l i)) ^ m := by
      have : y0 = (a : D.nd.O i) + y * ((D.nd.l i : ℕ) : D.nd.O i) ^ m := by rw [hy]; ring
      rw [this, map_add, map_mul, map_pow, map_natCast, map_natCast]
    have hq' : ((b : ℕ) : Formalism.BasicNotions.Loc.Om (D.nd.l i)) - (a : Formalism.BasicNotions.Loc.Om (D.nd.l i)) =
        ((D.nd.l i : ℕ) : Formalism.BasicNotions.Loc.Om (D.nd.l i)) ^ m * (q : Formalism.BasicNotions.Loc.Om (D.nd.l i)) := by
      have := congrArg (Int.cast : ℤ → Formalism.BasicNotions.Loc.Om (D.nd.l i)) hq
      push_cast at this
      exact this
    have hsplit : ψ y0 - algebraMap ℚ_[D.nd.l i] (Formalism.BasicNotions.Loc.Om (D.nd.l i)) X =
        (-(((D.nd.l i : ℕ) : Formalism.BasicNotions.Loc.Om (D.nd.l i)) ^ m * (q : Formalism.BasicNotions.Loc.Om (D.nd.l i))) +
          ψ y * ((D.nd.l i : ℕ) : Formalism.BasicNotions.Loc.Om (D.nd.l i)) ^ m) +
        algebraMap ℚ_[D.nd.l i] (Formalism.BasicNotions.Loc.Om (D.nd.l i)) ((b : ℚ_[D.nd.l i]) - X) := by
      rw [hy0', ← hq', map_sub, map_natCast]
      ring
    have hB : ∀ z : Formalism.BasicNotions.Loc.Om (D.nd.l i), ‖z‖ ≤ 1 →
        ‖z * ((D.nd.l i : ℕ) : Formalism.BasicNotions.Loc.Om (D.nd.l i)) ^ m‖ ≤ (((D.nd.l i : ℕ) : ℝ)⁻¹) ^ m := by
      intro z hz
      rw [norm_mul, norm_pow, hl]
      exact mul_le_of_le_one_left (pow_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) _) hz
    have h1 : ‖-(((D.nd.l i : ℕ) : Formalism.BasicNotions.Loc.Om (D.nd.l i)) ^ m * (q : Formalism.BasicNotions.Loc.Om (D.nd.l i)))‖ ≤
        (((D.nd.l i : ℕ) : ℝ)⁻¹) ^ m := by
      rw [norm_neg, mul_comm]
      exact hB _ (hint q)
    have h2 := hB (ψ y) (hψ1 y)
    have h3 : ‖algebraMap ℚ_[D.nd.l i] (Formalism.BasicNotions.Loc.Om (D.nd.l i)) ((b : ℚ_[D.nd.l i]) - X)‖ ≤
        (((D.nd.l i : ℕ) : ℝ)⁻¹) ^ m := by
      rw [PadicAlgCl.norm_extends, norm_sub_rev, inv_pow, ← zpow_natCast, ← zpow_neg]
      exact hXb
    rw [hsplit]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ h3)
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)
  have hl1 : (1 : ℝ) < ((D.nd.l i : ℕ) : ℝ) := by exact_mod_cast hp.one_lt
  by_contra hne
  have hpos : 0 < ‖ψ y0 - algebraMap ℚ_[D.nd.l i] (Formalism.BasicNotions.Loc.Om (D.nd.l i)) X‖ :=
    norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hpos (inv_lt_one_of_one_lt₀ hl1)
  exact absurd (key m) (not_le.2 hm)

end Cyc

section Row

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

theorem cycMatch [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
    [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))] [IsDiscreteValuationRing (D.nd.O i)] {w : ℕ}
    {VT VT' : Type}
    [AddCommGroup VT] [Module (D.nd.O i) VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul (D.nd.O i) VT]
    [AddCommGroup VT'] [Module (D.nd.O i) VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul (D.nd.O i) VT']
    (Dat : Formalism.RepresentationBoundsCohomology.LOC.LatData (D.nd.O i) ↥(Γn i dc w) VT VT')
    (hε : ∀ g : ↥(Γn i dc w), Dat.ε g = epsU D.nd i (g : GE D.nd))
    (hn : K.plOf i dc w ∈ placesOver D.host.E (D.nd.l i)) :
    KBKa.CycMatch Dat (eK (D.nbr i _ hn)) (Br.iota D.nbr i _ hn) (Br.PD D.loc D.nbr i _ hn) := by
  intro g
  rw [hε]
  apply Subtype.ext
  have hχ : (((Br.PD D.loc D.nbr i _ hn).χ g : ℚ_[D.nd.l i]ˣ) : ℚ_[D.nd.l i]) =
      (((D.loc (D.nd.l i)).χQ (g : Formalism.BasicNotions.Loc.GQ (D.nd.l i)) : ℚ_[D.nd.l i]ˣ) : ℚ_[D.nd.l i]) :=
    (D.loc (D.nd.l i)).PD_χ _ g
  show _ = ((algebraMap ℚ_[D.nd.l i] (Br.LLw (D.nbr i _ hn))
    (((Br.PD D.loc D.nbr i _ hn).χ g : ℚ_[D.nd.l i]ˣ) : ℚ_[D.nd.l i]) : Br.LLw (D.nbr i _ hn)) :
      Formalism.BasicNotions.Loc.Om (D.nd.l i))
  rw [hχ]
  exact eps_eq_chiQ i hn g

theorem rowIn_lat {t : ℕ} {d : Type} (bl : d → Fin (t + 1)) [Fintype d]
    [τK : TopologicalSpace (FractionRing (D.nd.O i))] (htop : τK = K.Topo.fracTopology (D.nd.O i))
    [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
    [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))] [IsDiscreteValuationRing (D.nd.O i)]
    (Dat : ∀ w, Formalism.RepresentationBoundsCohomology.LOC.LatData (D.nd.O i) ↥(Γn i dc w) (KLat.VT (O := D.nd.O i) bl w)
      (KLat.VT (O := D.nd.O i) bl w))
    [∀ w, Module (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT)]
    [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT)]
    [∀ w, Module (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]
    [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]
    (hε : ∀ w (g : ↥(Γn i dc w)), (Dat w).ε g = epsU D.nd i (g : GE D.nd))
    (hdR : ∀ w (hn : K.plOf i dc w ∈ placesOver D.host.E (D.nd.l i)),
      IsDR (Br.PD D.loc D.nbr i _ hn) (repL (eK (D.nbr i _ hn)) (Dat w).ρT (Br.iota D.nbr i _ hn)))
    (w : ℕ) :
    KBKa.RowIn i dc (KLat.VT (O := D.nd.O i) bl) (KLat.VT (O := D.nd.O i) bl) Dat w := by
  intro hn
  refine ⟨?_, ?_, ?_, cycMatch i dc (Dat w) (hε w) hn, hdR w hn⟩
  · subst htop
    exact homeoK i hn
  · subst htop
    exact topMatch_pi i hn _
  · subst htop
    exact topMatch_pi i hn _

end Row

section RowTop

theorem cont_of_tr {O : Type} [CommRing O] {LL : Type} [Field LL] [TopologicalSpace LL] (e : FractionRing O ≃+* LL)
    {Γ G : Type} [Group Γ] [TopologicalSpace Γ] [Group G] [TopologicalSpace G] (ι : G →* Γ)
    (hι : KBKa.IotaHomeo ι) {V : Type} [AddCommGroup V] [Module (FractionRing O) V] [t : TopologicalSpace V]
    (ht : KBKa.TopMatch e V) (c : Γ → V) (hc : Continuous fun g => (show TrV e V from c (ι g))) : Continuous c := by
  obtain ⟨h, hh⟩ := hι
  subst ht
  have h3 : Continuous fun γ => (show TrV e V from c (ι (h.symm γ))) := hc.comp h.symm.continuous
  have key : (fun γ => (show TrV e V from c (ι (h.symm γ)))) = c := funext fun γ => by
    show c (ι (h.symm γ)) = c γ
    rw [← hh, Homeomorph.apply_symm_apply]
  rw [key] at h3
  exact h3

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

theorem rowTop_pi {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) {w : ℕ}
    (hn : K.plOf i dc w ∈ placesOver D.host.E (D.nd.l i)) (n : Type) [Finite n] :
    letI := K.Topo.fracTopology (D.nd.O i)
    ∀ c : ↥(Γn i dc w) → (n → FractionRing (D.nd.O i)),
      Continuous (fun g => (show TrV (eK (D.nbr i _ hn)) (n → FractionRing (D.nd.O i)) from
        c (Br.iota D.nbr i _ hn g))) → Continuous c := by
  letI := K.Topo.fracTopology (D.nd.O i)
  intro c hc
  exact cont_of_tr (eK (D.nbr i _ hn)) (Br.iota D.nbr i _ hn) (iotaHomeo i hn) (topMatch_pi i hn n) c hc

end RowTop

section Ms

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

theorem rTwO_cont (hc : TruncatedSeriesCountingIdentities.FamilyContinuous i r) (x : D.nd.X i) : Continuous (rTwO D.nd i r x) := by
  have hχ : Continuous fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i) := by
    have e : (fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i)) =
        fun g => ((chiU D.nd i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
      funext g
      rw [MonoidHom.inv_apply, map_inv]
    rw [e]
    exact (D.nd.chi_cont i 1).comp continuous_inv
  exact hχ.smul (hc x)

theorem locC_cont (hc : TruncatedSeriesCountingIdentities.FamilyContinuous i r) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i) :
    Continuous ⇑(TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x)) := by
  have hinc : Continuous (TruncatedSeriesCountingIdentities.CoefExt.inc C) :=
    continuous_induced_rng.2 (by exact continuous_subtype_val)
  have h1 : Continuous fun g : Br.G D.nbr i w hw =>
      rTwO D.nd i r x ((Br.iota D.nbr i w hw g : _) : GE D.nd) :=
    (rTwO_cont i r hc x).comp (continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw))
  exact ((h1.matrix_map (D.nbr i w hw).eO_cont).matrix_map continuous_subtype_val).matrix_map hinc

end Ms

end Formalism.MainNotions.N.KOrb

end
