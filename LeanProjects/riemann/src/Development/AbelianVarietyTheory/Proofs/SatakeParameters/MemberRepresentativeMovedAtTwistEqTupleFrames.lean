import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroClassesBijectiveSameDeco
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicPointDecoratedLatticeAllTwists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberLevelPrimeNotMemUnderLevelPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalGroupElementEqLevelComponentBadPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalMoveClassRepIffLocalConditions
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyEquivClassSet
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.ZeroMove

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adAt_entry_of_bc {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) {η η' : GL (Fin n) (AfE F E)}
    (h : bc (prV (E := E) (P.under (𝓞 F))) η = bc (prV (E := E) (P.under (𝓞 F))) η') (i j : Fin n) :
    adAt F P (η.1 i j) = adAt F P (η'.1 i j) := by
  have e := congrArg (fun z : GL (Fin n) (E ⊗[F] (P.under (𝓞 F)).adicCompletion F) => z.1 i j) h
  exact AdT.LocSplice.adAt_eq_of_prV P e

theorem adAt_entry_one {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) {η : GL (Fin n) (AfE F E)}
    (h : bc (prV (E := E) (P.under (𝓞 F))) η = 1) (i j : Fin n) :
    adAt F P (η.1 i j) = if i = j then 1 else 0 := by
  rw [adAt_entry_of_bc P (η' := 1) (h.trans (map_one _).symm) i j, Units.val_one, Matrix.one_apply]
  split_ifs <;> simp

theorem adAt_mul_entry {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (g κ : GL (Fin n) (AfE F E)) (i j : Fin n) :
    adAt F P ((g * κ).1 i j) = ∑ l, adAt F P (g.1 i l) * adAt F P (κ.1 l j) := by
  rw [Units.val_mul, Matrix.mul_apply, map_sum]
  simp only [map_mul]

theorem adAt_mul_of_one {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) (AfE F E)) {κ : GL (Fin n) (AfE F E)}
    (h : bc (prV (E := E) (P.under (𝓞 F))) κ = 1) (i j : Fin n) :
    adAt F P ((g * κ).1 i j) = adAt F P (g.1 i j) := by
  rw [adAt_mul_entry]
  simp only [adAt_entry_one P h, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem adAt_mul_congr {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) (AfE F E)) {κ κ' : GL (Fin n) (AfE F E)}
    (h : bc (prV (E := E) (P.under (𝓞 F))) κ = bc (prV (E := E) (P.under (𝓞 F))) κ') (i j : Fin n) :
    adAt F P ((g * κ).1 i j) = adAt F P ((g * κ').1 i j) := by
  rw [adAt_mul_entry, adAt_mul_entry]
  simp only [adAt_entry_of_bc P h]

theorem adAt_pullV_mul {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) (AfE F E)) {κ : GL (Fin n) (AfE F E)}
    (h : bc (prV (E := E) (P.under (𝓞 F))) κ = 1) (x : Sp E n) (i : Fin n) :
    adAt F P (pullV (g * κ) x i) = adAt F P (pullV g x i) := by
  have h' : bc (prV (E := E) (P.under (𝓞 F))) κ⁻¹ = 1 := by rw [map_inv, h, inv_one]
  unfold pullV
  rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec, dotProduct, map_sum]
  simp only [map_mul, adAt_entry_one P h', ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem comm_of_bc {n : ℕ} (κ k : GL (Fin n) (AfE F E))
    (h : ∀ v, bc (prV (E := E) v) κ = 1 ∨ bc (prV (E := E) v) k = 1) : κ * k = k * κ := by
  refine Units.ext (Matrix.ext fun i j => PtExist.ad_ext fun P => ?_)
  refine adAt_entry_of_bc P ?_ i j
  rcases h (P.under (𝓞 F)) with h1 | h1 <;> simp [map_mul, h1]

theorem exists_splice {n : ℕ} (sg : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (W : Finset (HeightOneSpectrum (𝓞 F)))
    (x : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hx : x ∈ UPts sg J (FiniteAdeleRing (𝓞 F) F)) :
    ∃ κ ∈ UPts sg J (FiniteAdeleRing (𝓞 F) F), (∀ v ∈ W, bc (prV (E := E) v) κ = bc (prV (E := E) v) x) ∧
      ∀ v ∉ W, bc (prV (E := E) v) κ = 1 := by
  classical
  have hne : ∀ (v w : HeightOneSpectrum (𝓞 F)), w ≠ v → ∀ (h : GL (Fin n) (E ⊗[F] v.adicCompletion F))
      (k : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
      bc (prV (E := E) w) (Formalism.UG.P.afsplitU v h k) = bc (prV (E := E) w) k := by
    intro v w hw h k
    apply Units.ext
    rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplitU_coe, Formalism.UG.P.afsplitC_prV_ne v w hw,
      ← Formalism.UG.P.afsplit_coe_bc_prV]
  induction W using Finset.induction_on with
  | empty => exact ⟨1, one_mem _, fun v hv => absurd hv (Finset.notMem_empty v), fun v _ => map_one _⟩
  | insert v W hvW ih =>
    obtain ⟨κ, hκ, h1, h2⟩ := ih
    refine ⟨Formalism.UG.P.afsplitU v (bc (prV (E := E) v) x) κ,
      Formalism.UG.P.afsplitU_mem v sg J _ _ (Formalism.UG.P.afsplit_bc_mem sg J v x hx) hκ, fun w hw => ?_, fun w hw => ?_⟩
    · by_cases e : w = v
      · subst e
        exact Formalism.UG.P.afsplit_right1 _ _ _
      · rw [hne v w e]
        exact h1 w ((Finset.mem_insert.1 hw).resolve_left e)
    · have e : w ≠ v := fun e => hw (e ▸ Finset.mem_insert_self _ _)
      rw [hne v w e]
      exact h2 w fun h => hw (Finset.mem_insert_of_mem h)

theorem carries_of_local [StarRing E] {n : ℕ} (x z : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hx : Formalism.L2.Herm.Carries x (stdLat E n) (stdLat E n))
    (h : ∀ v, bc (prV (E := E) v) z = bc (prV (E := E) v) x ∨ bc (prV (E := E) v) z = 1) :
    Formalism.L2.Herm.Carries z (stdLat E n) (stdLat E n) := by
  classical
  haveI : Module.Finite (𝓞 E) (stdLat E n) := Module.Finite.iff_fg.2 (stdLat_lattice (E := E) (n := n)).fg

  have helper : ∀ (A : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (v : HeightOneSpectrum (𝓞 F))
      (t : Fin n → E ⊗[F] v.adicCompletion F),
      A *ᵥ (fun i => Formalism.UG.P.afsplitIE v (t i)) ∈ Formalism.L2.Herm.hatL (F := F) (stdLat E n) ↔
        A.map (prV (E := E) v) *ᵥ t ∈ Formalism.L2.Herm.locL v (stdLat E n) := by
    intro A v t
    have hv : ∀ w, (fun i => prV (E := E) w ((A *ᵥ (fun i => Formalism.UG.P.afsplitIE v (t i))) i)) =
        A.map (prV (E := E) w) *ᵥ (fun i => prV (E := E) w (Formalism.UG.P.afsplitIE v (t i))) := fun w => by
      funext i
      rw [RingHom.map_mulVec]
      rfl
    rw [GlobalTheory.LevPin.mem_hatL_iff]
    constructor
    · intro h
      have := h v
      rwa [hv v, funext fun i => Formalism.UG.P.afsplit_prV_IE v (t i)] at this
    · intro h w
      rw [hv w]
      by_cases e : w = v
      · subst e
        rwa [funext fun i => Formalism.UG.P.afsplit_prV_IE w (t i)]
      · rw [funext fun i => Formalism.UG.P.afsplit_prV_IE_ne v w e (t i)]
        have e0 : (fun _ : Fin n => (0 : E ⊗[F] w.adicCompletion F)) = 0 := rfl
        rw [e0, Matrix.mulVec_zero]
        exact Submodule.zero_mem _
  have key : ∀ v (t : Fin n → E ⊗[F] v.adicCompletion F), t ∈ Formalism.L2.Herm.locL v (stdLat E n) ↔
      (((bc (prV (E := E) v) z)⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ t ∈ Formalism.L2.Herm.locL v (stdLat E n) := by
    intro v t
    rcases h v with e | e
    · rw [e]
      have h1 := helper 1 v t
      have h2 := helper ((x⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) v t
      have h3 := hx (fun i => Formalism.UG.P.afsplitIE v (t i))
      rw [Matrix.one_mulVec, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec] at h1
      rw [← map_inv, Formalism.UG.P.afsplit_coe_bc_prV]
      exact h1.symm.trans (h3.trans h2)
    · rw [e, inv_one, Units.val_one, Matrix.one_mulVec]
  intro y
  rw [GlobalTheory.LevPin.mem_hatL_iff, GlobalTheory.LevPin.mem_hatL_iff]
  refine forall_congr' fun v => ?_
  rw [key v]
  have e : (fun i => prV (E := E) v ((((z⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ y) i)) =
      (((bc (prV (E := E) v) z)⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ fun i => prV (E := E) v (y i) := by
    funext i
    rw [RingHom.map_mulVec, ← map_inv, Formalism.UG.P.afsplit_coe_bc_prV]
    rfl
  rw [e]

omit [NumberField F] [Algebra F E] in

theorem ptFr_eq [StarRing E] {n : ℕ} {ST SG Q Q' : Finset (HeightOneSpectrum (𝓞 E))} (p : DecoF E n ST SG Q)
    (p' : DecoF E n ST SG Q') (hd : p.deco = p'.deco) {P : HeightOneSpectrum (𝓞 E)} (h : P ∉ Q) (h' : P ∉ Q') :
    ptFr p P = ptFr p' P := by
  by_cases hs : P ∈ SG
  · simp only [ptFr, dif_pos hs, hd]
  · simp only [ptFr, dif_neg hs, dif_neg h, dif_neg h', hd]

end Gen

end GlobalTheory.Mem.Col2.ZeroMove

namespace GlobalTheory.Mem.Col2.ZeroMove

section Core

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]

set_option maxHeartbeats 800000 in

theorem coreGen (hc : CMData F E) {n : ℕ} {ST SG Q0 Q1 SQ : Finset (HeightOneSpectrum (𝓞 E))}
    (W : Finset (HeightOneSpectrum (𝓞 F))) (p0 : DecoF E n ST SG Q0) (p1 : DecoF E n ST SG Q1)
    (hdeco : p1.deco = p0.deco) (hQ0 : ∀ P, P ∉ Q0) (hQ1 : ∀ P ∈ Q1, P.under (𝓞 F) ∈ W)
    (hoff : ∀ P, P ∈ ST ∨ P ∈ SG → P.under (𝓞 F) ∉ W) (y k g1 : GL (Fin n) (AfE F E))
    (hk : ∀ v ∈ W, bc (prV (E := E) v) k = 1) (hpt : IsPtOf hc (y * k) (extTo SQ p0))
    (hg1 : IsPtOf hc g1 (extTo SQ p1)) :
    ∃ κ : GL (Fin n) (AfE F E), (∀ v ∉ W, bc (prV (E := E) v) κ = 1) ∧ IsPtOf hc (y * κ * k) (extTo SQ p1) ∧
      IsPtOf hc (y * κ * k) p0 := by
  classical
  have hN : (extTo SQ p1).deco.1.N = (extTo SQ p0).deco.1.N := by
    show p1.deco.1.N = p0.deco.1.N
    rw [hdeco]
  have hxU : (y * k)⁻¹ * g1 ∈ UPts hc.sig 1 (FiniteAdeleRing (𝓞 F) F) :=
    mul_mem (inv_mem hpt.uni) hg1.uni
  have hxC : Formalism.L2.Herm.Carries ((y * k)⁻¹ * g1) (stdLat E n) (stdLat E n) := by
    intro z
    have e1 := hpt.lat (((y * k : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) _) *ᵥ z)
    have e2 := hg1.lat (((y * k : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) _) *ᵥ z)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at e1
    rw [hN] at e2
    rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, ← Matrix.mulVec_mulVec, ← e2, e1]
  obtain ⟨κ, hκU, hκin, hκout⟩ := exists_splice hc.sig 1 W ((y * k)⁻¹ * g1) hxU
  have hκC : Formalism.L2.Herm.Carries κ (stdLat E n) (stdLat E n) :=
    carries_of_local _ κ hxC fun v => if hv : v ∈ W then Or.inl (hκin v hv) else Or.inr (hκout v hv)
  have hcomm : κ * k = k * κ :=
    comm_of_bc κ k fun v => if hv : v ∈ W then Or.inr (hk v hv) else Or.inl (hκout v hv)
  have hmv : y * κ * k = y * k * κ := by rw [mul_assoc, hcomm, ← mul_assoc]
  have hof : ∀ P : HeightOneSpectrum (𝓞 E), (P ∈ ST ∨ P ∈ SG) → bc (prV (E := E) (P.under (𝓞 F))) κ = 1 :=
    fun P hP => hκout _ (hoff P hP)
  have hd' : (extTo SQ p1).deco = (extTo SQ p0).deco := hdeco
  have h1 : IsPtOf hc (y * κ * k) (extTo SQ p1) := by
    rw [hmv]
    refine ⟨mul_mem hpt.uni hκU, ?_, fun P x hx i hi => ?_, fun w x hx i => ?_, fun P i j => ?_⟩
    · rw [hN]
      exact GlobalTheory.Mem.Col2.TC.ChTw.Match.LocForm.carries_mul hpt.lat hκC
    · rw [adAt_pullV_mul P.1 (y * k) (hof P.1 (Or.inl P.2)), hd']
      exact hpt.f P x (by rw [← hN]; exact hx) i hi
    · rw [adAt_pullV_mul w.1 (y * k) (hof w.1 (Or.inr w.2)), hd']
      exact hpt.be w x (by rw [← hN]; exact hx) i
    · by_cases hv : P.1.under (𝓞 F) ∈ W
      · rw [adAt_mul_congr P.1 (y * k) (hκin _ hv) i j, mul_inv_cancel_left]
        exact hg1.fr P i j
      · have hQa : P.1 ∉ Q1 := fun h => hv (hQ1 _ h)
        rw [adAt_mul_of_one P.1 (y * k) (hκout _ hv) i j, hpt.fr P i j, extTo_fr, extTo_fr,
          ptFr_eq p0 p1 hdeco.symm (hQ0 P.1) hQa]
  refine ⟨κ, hκout, h1, ⟨h1.uni, ?_, fun P x hx i hi => ?_, fun w x hx i => ?_, fun P => absurd P.2 (hQ0 P.1)⟩⟩
  · have e := h1.lat
    rw [hN] at e
    exact e
  · have e := h1.f P x (by rw [hN]; exact hx) i hi
    rw [hd'] at e
    exact e
  · have e := h1.be w x (by rw [hN]; exact hx) i
    rw [hd'] at e
    exact e

end Core

end GlobalTheory.Mem.Col2.ZeroMove

namespace GlobalTheory.Mem.Col2.ZeroMove

theorem not_underQ {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (u : B.Word) (a : I.ι) {P : HeightOneSpectrum (𝓞 B.fields.E)}
    (hP : P ∈ (B.primes X).vT u ∨ P ∈ (B.primes X).vGs) : ¬ I.UnderQ a (P.under (𝓞 B.host.F)) := by
  rintro ⟨P', hP', e⟩
  have hg := (LevTwist.good_of_mem hOk (ColIn.Q_subset_SQ I a hP')).2.2.2
  rw [e] at hg
  rcases hP with hP | hP
  · have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1
    have hT0 : (B.primes X).piT u ≠ 0 := fun h => by
      have := hPr.piT_norm u
      rw [h, zero_mul] at this
      exact (hPr.T_prime u).ne_zero (Nat.cast_eq_zero.1 this.symm)
    have hE : (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∈ P.asIdeal := by
      rw [← hPr.piT_norm u]
      exact Ideal.mul_mem_right _ _ ((mem_divs hT0 P).1 hP)
    have e2 := (ReadTwist.plc_under_eq_iff (F := B.host.F) P (hPr.T_prime u)).2 hE
    exact hg (e2 ▸ hOk.T_mem u)
  · exact hg (LevTwist.plc_mem hOk hP)

set_option maxHeartbeats 800000 in

theorem main : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))), (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.StdF l Z u F → ∀ (k : GA B (B.R.N 0)), I.Reads u I.mu0 0 (fun _ => ()) (fun _ => F.to0.cls0.lev.Lb) (fun _ => F.to0.cls0.lev.U) (fun _ => F.to0.cls0.lev.chi) (fun c => (F.to0.cls0.y c).1) (fun c s => (F.to0.cls0.stabI c s).1) (fun _ => k) → ∀ c, ∃ κ : F.to0.cls0.lev.U, (∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) ∧ F.to0.cls0.lev.chi κ = 1 ∧ PtOf (B := B) ((show GA B (B.R.N 0) from (F.to0.cls0.y c).1 * κ.1) * k) (extTo I.SQ ((I.stp u a 0).rep (I.eCls0 l u a c)).1.1) := by
  intro B X I hOk hPins l Z u Ch0 chOf0 F a Q hQ hStd k hR c
  classical
  have hk : ∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) k = 1 := by
    intro v hv
    obtain ⟨P, hP, hPv⟩ := (hQ v).1 hv
    refine hR.k_off () v ?_ ?_ (Or.inl rfl)
    · rw [← hPv]
      exact LevTwist.T_notMem_under_uSG B X I hOk u P (Finset.mem_union_right _ (ColIn.Q_subset_SQ I a hP))
    · rintro ⟨P', hP', -⟩
      rw [ColIn.twistPrimes_reference_tuple_eq_empty] at hP'
      exact Finset.notMem_empty _ hP'
  have hdeco : ((I.stp u a 0).rep (I.eCls0 l u a c)).1.1.deco = ((I.stp u I.mu0 0).rep c).1.1.deco :=
    ClsZero.stepZero_corresponding_representatives_same_deco hOk u a (l.idx0 a).some c
  obtain ⟨g1, hg1⟩ := PtTwist.exists_ptOf_twists I hOk u _ (extTo I.SQ ((I.stp u a 0).rep (I.eCls0 l u a c)).1.1)
  have hQ0 : ∀ P, P ∉ I.Q I.mu0 := fun P h => by
    rw [ColIn.twistPrimes_reference_tuple_eq_empty] at h
    exact Finset.notMem_empty _ h
  obtain ⟨κ, hκout, h1, h0⟩ := coreGen B.sp.cm Q _ _ hdeco hQ0 (fun P h => (hQ _).2 ⟨P, h, rfl⟩)
    (fun P hP hv => not_underQ I hOk u a hP ((hQ _).1 hv)) _ k g1 hk (hR.pt c) hg1
  have e1 : (I.stp u I.mu0 0).act c.1 1 ((I.stp u I.mu0 0).rep c) = (I.stp u I.mu0 0).rep c :=
    @one_smul _ _ _ ((I.stp u I.mu0 0).actD c.1) _
  have hkeep := AdT.keeps_one I ((I.stp u I.mu0 0).rep c)
  have hmem : κ ∈ F.to0.cls0.lev.U :=
    (hR.lev c κ _ h0).2 ⟨1, hkeep.1, by rw [e1], hkeep.2⟩
  have hchi : F.to0.cls0.lev.chi ⟨κ, hmem⟩ = 1 := by
    have h := hR.chr c ⟨κ, hmem⟩ 1 hkeep.1 (by rw [e1]; exact h0)
    rw [map_one, Units.val_one, map_one] at h
    exact Units.ext h
  exact ⟨⟨κ, hmem⟩, hκout, hchi, h1⟩

end GlobalTheory.Mem.Col2.ZeroMove
