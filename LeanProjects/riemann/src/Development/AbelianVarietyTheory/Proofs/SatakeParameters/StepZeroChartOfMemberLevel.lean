import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsChartsReadingStepZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroClassesBijectiveSameDeco
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwU.AtTrue.ZeroChart

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem latAt_eCls0 (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) (c : (I.stp u I.mu0 0).Cl) :
    I.latAt u a 0 (I.eCls0 l u a c) = I.latAt u I.mu0 0 c := by
  have e : I.eCls0 l u a c = I.cl0 u a (l.idx0 a).some c := rfl
  unfold TC.latAt
  rw [dif_pos (Nat.zero_le _), dif_pos (Nat.zero_le _), e, ClsZero.stepZero_corresponding_representatives_same_deco hI]

theorem range_eCls0 (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) (c : (I.stp u I.mu0 0).Cl)
    (γ : GL (Fin (B.R.N 0)) B.host.E) :
    γ ∈ (MemChart.stM (Chart0.lvG I a) (Chart0.lvQ I a) ((I.Tp a).pref u 0) (I.pref u a 0) (I.eCls0 l u a c)).range ↔
      γ ∈ (MemChart.stM (Chart0.lvG I I.mu0) (Chart0.lvQ I I.mu0) ((I.Tp I.mu0).pref u 0) (I.pref u I.mu0 0) c).range := by
  rw [Chart0.stab_range0 I hI, Chart0.stab_range0 I hI]
  have e : I.eCls0 l u a c = I.cl0 u a (l.idx0 a).some c := rfl
  rw [e, ClsZero.stepZero_corresponding_representatives_same_deco hI]

theorem map_conj_mul {G : Type} [Group G] (U : Subgroup G) (y k : G) (hk : k ∈ U) :
    U.map (MulAut.conj (y * k)).toMonoidHom = U.map (MulAut.conj y).toMonoidHom := by
  ext g
  constructor
  · rintro ⟨x, hx, hg⟩
    refine ⟨k * x * k⁻¹, (conj_mem_iff hk x).2 hx, Eq.trans ?_ hg⟩
    show y * (k * x * k⁻¹) * y⁻¹ = y * k * x * (y * k)⁻¹
    group
  · rintro ⟨x, hx, hg⟩
    refine ⟨k⁻¹ * x * k, by simpa using (conj_mem_iff (inv_mem hk) x).2 hx, Eq.trans ?_ hg⟩
    show y * k * (k⁻¹ * x * k) * (y * k)⁻¹ = y * x * y⁻¹
    group

end GlobalTheory.TwU.AtTrue.ZeroChart

end

namespace GlobalTheory.TwU.AtTrue.ZeroChart

open scoped TensorProduct

set_option maxHeartbeats 4000000 in

theorem chart_of_member : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClsTied (D := (I.rec7 l Z)) u 0 (Nat.zero_le _)) (κ : (I.stp u I.mu0 0).Cl → K.lev.U), (∀ c s, (K.stabI c s).1 = (I.stp u I.mu0 0).gam c.1 s.1) → ∃ K0 : Fam I l Z u a 0 (Nat.zero_le _) (badQ (I.rec7 l Z) Q) (fun _ => ()), (K0 ()).lev.Lb = K.lev.Lb ∧ (K0 ()).lev.Uloc = K.lev.Uloc ∧ (K0 ()).lev.U = K.lev.U ∧ (∀ (x : (K0 ()).lev.U) (x' : K.lev.U), x.1 = x'.1 → (K0 ()).lev.chi x = K.lev.chi x') ∧ (∀ c, ((K0 ()).y ⟨I.eCls0 l u a c, rfl⟩).1 = (K.y c).1 * (κ c).1) ∧ ∀ c s, ((K0 ()).stabI c s).1 = (I.stp u a 0).gam c.1.1 s.1 := by
  intro B X I hI hP l Z u a Q K κ hK
  have hi : 0 ≤ B.R.m := Nat.zero_le _
  let e := I.eCls0 l u a
  have hU : ∀ c, (κ c).1 ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) 0 hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) :=
    fun c => ((K.lev.U_eq _).1 (κ c).2).1
  let κU : ∀ c, UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) 0 hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) :=
    fun c => ⟨(κ c).1, hU c⟩
  have hL : ∀ c, (κ c).1 ∈ levelAfL (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) 0 hi) K.lev.Lb := fun c =>
    (GlobalTheory.LatticeStabLocal.mem_levelAfL_iff _ _ _ _ _ _ K.lev.Lb_fin _).2
      ⟨hU c, fun v => K.lev.Uloc_lev v (((K.lev.U_eq _).1 (κ c).2).2 v)⟩
  have hlat : ∀ c'', I.latAt u a 0 c'' = I.latAt u I.mu0 0 (e.symm c'') := by
    intro c''
    obtain ⟨c, rfl⟩ := e.surjective c''
    rw [e.symm_apply_apply]
    exact latAt_eCls0 I hI l u a c
  have hrng : ∀ c'' (γ : GL (Fin (B.R.N 0)) B.host.E),
      γ ∈ (MemChart.stM (Chart0.lvG I a) (Chart0.lvQ I a) ((I.Tp a).pref u 0) (I.pref u a 0) c'').range ↔
      γ ∈ (MemChart.stM (Chart0.lvG I I.mu0) (Chart0.lvQ I I.mu0) ((I.Tp I.mu0).pref u 0) (I.pref u I.mu0 0) (e.symm c'')).range := by
    intro c'' γ
    obtain ⟨c, rfl⟩ := e.surjective c''
    rw [e.symm_apply_apply]
    exact range_eCls0 I hI l u a c γ
  have hmem : ∀ c'' (s : (I.stp u a 0).Stab c''),
      MemChart.stM (Chart0.lvG I a) (Chart0.lvQ I a) ((I.Tp a).pref u 0) (I.pref u a 0) c'' s ∈
        UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) 0 hi) := by
    intro c'' s
    obtain ⟨t, ht⟩ := (hrng c'' _).1 ⟨s, rfl⟩
    rw [← ht]
    exact (congrArg (fun g => g ∈ UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) 0 hi))
      (hK (e.symm c'') t)).mp (K.stabI (e.symm c'') t).2
  have hcls : ∀ c, (Quotient.mk'' (K.y c * κU c) : Cls K.lev) = Quotient.mk'' (K.y c) := fun c => by
    refine (DoubleCoset.eq _ _ _ _).2 ⟨1, one_mem _, (κU c)⁻¹, ?_, by group⟩
    exact inv_mem (κ c).2
  refine ⟨fun _ =>
    { lev :=
        { K.lev with
          Uloc_hyp := fun v hv hT => K.lev.Uloc_hyp v (fun h => hv (Or.inl h)) hT
          chi_triv := fun x hx => K.lev.chi_triv x (fun v hv => hx v (Or.inl hv)) }
      y := fun c' => K.y (e.symm c'.1) * κU (e.symm c'.1)
      y_bij := ?_
      y_lat := ?_
      stabI := fun c' => (MemChart.stM (Chart0.lvG I a) (Chart0.lvQ I a) ((I.Tp a).pref u 0) (I.pref u a 0) c'.1).codRestrict _ (hmem c'.1)
      stabI_inj := fun c' s t h => MemChart.stM_inj (Chart0.lvG I a) (Chart0.lvQ I a) _ _ ((l.ch u a).step 0) c'.1 (congrArg Subtype.val h)
      stabI_range := ?_ }, rfl, rfl, rfl, fun x x' h => ?_, fun c => ?_, fun c s => rfl⟩
  · convert K.y_bij.comp (e.symm.bijective.comp
        (Equiv.subtypeUnivEquiv (p := fun c' : (I.stp u a 0).Cl => (fun _ => ()) c' = ()) (fun _ => rfl)).bijective) using 1
    funext c'
    exact hcls (e.symm c'.1)
  · intro c' x
    rw [hlat c'.1]
    refine (K.y_lat (e.symm c'.1) x).trans ?_
    show _ ↔ ((((K.y (e.symm c'.1)).1 * (κ (e.symm c'.1)).1)⁻¹).1 *ᵥ x ∈ _)
    rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
    exact (inv_mem (hL _)).2 _
  · intro c' γ
    have h1 : γ ∈ ((MemChart.stM (Chart0.lvG I a) (Chart0.lvQ I a) ((I.Tp a).pref u 0) (I.pref u a 0) c'.1).codRestrict _ (hmem c'.1)).range ↔
        γ.1 ∈ (MemChart.stM (Chart0.lvG I a) (Chart0.lvQ I a) ((I.Tp a).pref u 0) (I.pref u a 0) c'.1).range :=
      ⟨fun ⟨s, hs⟩ => ⟨s, congrArg Subtype.val hs⟩, fun ⟨s, hs⟩ => ⟨s, Subtype.ext hs⟩⟩
    refine h1.trans ((hrng c'.1 γ.1).trans (Iff.trans ?_ ((K.stabI_range (e.symm c'.1) γ).trans ?_)))
    · exact ⟨fun ⟨t, ht⟩ => ⟨t, Subtype.ext ((hK _ t).trans ht)⟩, fun ⟨t, ht⟩ => ⟨t, (hK _ t).symm.trans (congrArg Subtype.val ht)⟩⟩
    show _ ↔ _ ∈ K.lev.U.map (MulAut.conj ((K.y (e.symm c'.1)).1 * (κ (e.symm c'.1)).1)).toMonoidHom
    rw [map_conj_mul _ _ _ (κ _).2]
  · show K.lev.chi x = K.lev.chi x'
    exact congrArg K.lev.chi (Subtype.ext h)
  · show (K.y (e.symm (e c))).1 * (κ (e.symm (e c))).1 = _
    rw [e.symm_apply_apply]

end GlobalTheory.TwU.AtTrue.ZeroChart
