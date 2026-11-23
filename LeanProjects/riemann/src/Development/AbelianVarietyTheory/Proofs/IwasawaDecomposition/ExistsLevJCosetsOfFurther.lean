import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReGLMemLevelVL
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtRec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPlacesPrimeToLevelAndTypePrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepBeforeClNonempty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLevOffType
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RedMLevJ
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped TensorProduct
namespace GlobalTheory.Mem.Col2.TwistLevel

set_option maxHeartbeats 64000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem exists_levJ_cosets_of_further : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → (∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∃ (W : ∀ v, v ∈ Q → Subgroup (GL (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F))) (ψ : (∀ v : Q, ↥(W v.1 v.2)) →* ℂˣ), (∀ v hv, W v hv ≤ levelVL (I.rec7 l Z).sp.cm.sig ((I.rec7 l Z).sp.X (B.R.m - 1)).gram v Lb0) ∧ (∀ v hv, ∃ n : ℕ, 0 < n ∧ ∀ x, Formalism.L2.Herm.InPrinc (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (B.R.m - 1)) v n Lb0 x → x ∈ W v hv) ∧ (∀ β v hv, (K β).lev.Uloc v ≤ (W v hv).map (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom) ∧ (∀ β v hv, ((((K β).lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom).subgroupOf (W v hv)).FiniteIndex) ∧ (∀ β (κ : (K β).lev.U) (z : ∀ v : Q, ↥(W v.1 v.2)), (∀ v : Q, reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (z v).1 = bc (prV (E := (I.rec7 l Z).host.E) v.1) κ.1) → (∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ψ z)) → Nonempty (TwLevJ I l Z F Q u a chOf K) := by
  intro B X I hOk hPins l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hR hUl hchi hFur
  classical
  have hQb : ∀ v ∈ Q, ((B.T u : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal ∧ ∀ j, ((B.host.g j : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal :=
    fun v hv => underQ_prime_to_bad I hOk l u a v ((hQ v).1 hv)
  obtain ⟨H0, hH0L, hH0U⟩ := GlobalTheory.Mem.Col2.TC.levJ_herm_level I hOk hPins l Z u (F u) (hStd u) h1
  obtain ⟨W, ψ, hWl, hWQ, hWle, hWfi, hψ⟩ := hFur H0.Lb hH0L
  choose w hw using fun β0 : Ch0 u (B.R.m - 1) => GlobalTheory.Mem.Col2.TC.chartLev_stab_vec I hOk hPins l Z u (F u) (hStd u) (hfr u) h1 β0
  have hRed := GlobalTheory.Mem.Col2.TC.LevJRed.redM_levJ I hOk hPins l Z u (F u) (hStd u)
  obtain ⟨J, hJLb, hmemU, hJUl⟩ : ∃ J : Formalism.L2.Herm.StepLevelQ (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (B.R.m - 1)) (I.rec7 l Z).host.g (B.T u) B.R.f Q,
      J.Lb = H0.Lb ∧ (∀ x, x ∈ J.U ↔ x ∈ Formalism.L2.Herm.UAf (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (B.R.m - 1)) ∧
      ∀ v, bc (prV (E := (I.rec7 l Z).host.E) v) x ∈ ulocQ H0 Q W v) ∧ ∀ v, J.Uloc v = ulocQ H0 Q W v :=
    ⟨mkLevQ H0 Q W hWl hWQ (fun v hv i => (hQb v hv).2 i) (fun v hv => (hQb v hv).1), rfl, fun x => Iff.rfl, fun v => rfl⟩
  have hUP : ∀ x, reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ x ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) ↔
      x ∈ Formalism.L2.Herm.UAf (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (B.R.m - 1)) := fun x =>
    reGL_mem_UPts _ (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ _ rfl _ x
  have hbc : ∀ v (y : GL (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)),
      bc (prV (E := (I.rec7 l Z).host.E) v) (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ y) = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (bc (prV (E := (I.rec7 l Z).host.E) v) y) :=
    fun v y => Formalism.L2.G.bc_reGL _ _ y
  have hmap : ∀ (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (H : Subgroup (GL (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F))) y,
      reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ y ∈ H.map (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom ↔ y ∈ H := fun v H y => by
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hgQ : ∀ j v, ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal → v ∉ Q := fun j v hv hq => (hQb v hq).2 j hv
  have hJoff : ∀ (κ : J.U) v, v ∉ Q → reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (bc (prV (E := (I.rec7 l Z).host.E) v) κ.1) ∈ (F u).levJ.Uloc v := fun κ v hv => by
    have := ((hmemU _).1 κ.2).2 v
    rw [ulocQ_neg H0 Q W hv] at this
    rw [hH0U v]
    exact (hmap v _ _).2 this

  obtain ⟨k, hRd, -⟩ := id hR
  obtain ⟨k0, hR0⟩ := (hStd u).mid (B.R.m - 1) h1 (succ_pred_m B.R)
  let ι : Type := Σ j : Fin 2, {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}
  haveI : Finite ι := by
    haveI : ∀ j : Fin 2, Finite {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal} := fun j => by
      have hne : ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ≠ 0 := Nat.cast_ne_zero.2 (l.pr.g_prime j).ne_zero
      have hfin := Ideal.finite_factors (I := Ideal.span {((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F)}) (by
        rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hne)
      exact (hfin.subset fun v (hv : ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal) =>
        (Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hv))).to_subtype
    exact Finite.instSigma
  haveI : ∀ p : ι, Finite (kv (I.rec7 l Z).host.F p.2.1) := fun p => Formalism.UG.P.glint_finite_residueField p.2.1
  haveI hfinV : Finite (∀ p : ι, Fin ((I.rec7 l Z).R.N ((I.rec7 l Z).R.m - 1)) → kv (I.rec7 l Z).host.F p.2.1) := Pi.finite
  have hTy : ∀ (κ : J.U) j v (hv : ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal),
      reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (bc (prV (E := (I.rec7 l Z).host.E) v) κ.1) ∈ (F u).levJ.Uloc v := fun κ j v hv => hJoff κ v (hgQ j v hv)
  let φ : ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), J.U →* GL (Fin (B.R.N (B.R.m - 1))) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F) :=
    fun v => (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom.comp ((bc (prV (E := (I.rec7 l Z).host.E) v)).comp J.U.subtype)
  let ρ : J.U → ∀ p : ι, Matrix (Fin ((I.rec7 l Z).R.N ((I.rec7 l Z).R.m - 1))) (Fin ((I.rec7 l Z).R.N ((I.rec7 l Z).R.m - 1))) (kv (I.rec7 l Z).host.F p.2.1) :=
    fun κ p => redJS F u p.1 p.2.1 p.2.2 (bc (prV (E := (I.rec7 l Z).host.E) p.2.1) κ.1)
  have hρ1 : ρ 1 = 1 := by
    funext p
    show redM _ _ ((F u).gl.mat p.1 p.2.1 p.2.2 _ (φ p.2.1 1)) = 1
    rw [map_one (φ p.2.1)]
    exact (hRed p.1 p.2.1 p.2.2).1
  have hρm : ∀ a b, ρ (a * b) = ρ a * ρ b := fun a b => by
    funext p
    show redM _ _ ((F u).gl.mat p.1 p.2.1 p.2.2 _ (φ p.2.1 (a * b))) =
      redM _ _ ((F u).gl.mat p.1 p.2.1 p.2.2 _ (φ p.2.1 a)) * redM _ _ ((F u).gl.mat p.1 p.2.1 p.2.2 _ (φ p.2.1 b))
    rw [map_mul (φ p.2.1)]
    exact (hRed p.1 p.2.1 p.2.2).2 _ (hTy a p.1 p.2.1 p.2.2) _ (hTy b p.1 p.2.1 p.2.2)
  letI actV : MulAction J.U (∀ p : ι, Fin ((I.rec7 l Z).R.N ((I.rec7 l Z).R.m - 1)) → kv (I.rec7 l Z).host.F p.2.1) := actOfRed ρ hρ1 hρm

  have hWmem : ∀ (κ : J.U) (v : Q), bc (prV (E := (I.rec7 l Z).host.E) v.1) κ.1 ∈ W v.1 v.2 := fun κ v => by
    have := ((hmemU _).1 κ.2).2 v.1
    rwa [ulocQ_pos H0 Q W v.2] at this
  have hzQ1 : ∀ v : Q, bc (prV (E := (I.rec7 l Z).host.E) v.1) (1 : J.U).1 = 1 := fun v => by
    rw [OneMemClass.coe_one, map_one]
  have hzQm : ∀ (κ κ' : J.U) (v : Q), bc (prV (E := (I.rec7 l Z).host.E) v.1) (κ * κ').1 =
      bc (prV (E := (I.rec7 l Z).host.E) v.1) κ.1 * bc (prV (E := (I.rec7 l Z).host.E) v.1) κ'.1 := fun κ κ' v => by
    rw [Subgroup.coe_mul, map_mul]
  obtain ⟨zQ, hzQ⟩ : ∃ zQ : J.U →* (∀ v : Q, ↥(W v.1 v.2)), ∀ κ v, (zQ κ v).1 = bc (prV (E := (I.rec7 l Z).host.E) v.1) κ.1 :=
    ⟨{ toFun := fun κ v => ⟨bc (prV (E := (I.rec7 l Z).host.E) v.1) κ.1, hWmem κ v⟩
       map_one' := funext fun v => Subtype.ext (hzQ1 v)
       map_mul' := fun κ κ' => funext fun v => Subtype.ext (hzQm κ κ' v) }, fun _ _ => rfl⟩
  let Kc : Ch → ∀ v : Q, Subgroup ↥(W v.1 v.2) := fun β v =>
    (((K β).lev.Uloc v.1).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom).subgroupOf (W v.1 v.2)
  let Hs : Ch → Subgroup J.U := fun β => (K β).lev.U.comap ((reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom.comp J.U.subtype)
  let wv : Ch → ∀ p : ι, Fin ((I.rec7 l Z).R.N ((I.rec7 l Z).R.m - 1)) → kv (I.rec7 l Z).host.F p.2.1 := fun β p => w (g β) p.1 p.2.1 p.2.2
  have hH : ∀ β (κ : J.U), κ ∈ Hs β ↔ (∀ q, zQ κ q ∈ Kc β q) ∧ κ • wv β = wv β := by
    intro β κ
    have e1 : κ ∈ Hs β ↔ ∀ v, reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (bc (prV (E := (I.rec7 l Z).host.E) v) κ.1) ∈ (K β).lev.Uloc v := by
      show reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ κ.1 ∈ (K β).lev.U ↔ _
      rw [(K β).lev.U_eq]
      refine ⟨fun h v => (hbc v κ.1) ▸ h.2 v, fun h => ⟨(hUP _).2 ((hmemU _).1 κ.2).1, fun v => (hbc v κ.1).symm ▸ h v⟩⟩
    have e2 : ∀ q : Q, zQ κ q ∈ Kc β q ↔ reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (bc (prV (E := (I.rec7 l Z).host.E) q.1) κ.1) ∈ (K β).lev.Uloc q.1 := fun q => by
      show (zQ κ q).1 ∈ ((K β).lev.Uloc q.1).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom ↔ _
      rw [Subgroup.mem_comap, hzQ]
      rfl
    rw [e1]
    constructor
    · intro h
      refine ⟨fun q => (e2 q).2 (h q.1), ?_⟩
      funext p
      obtain ⟨j, v, hv⟩ := p
      have := h v
      rw [hUl β v (hgQ j v hv), hw (g β) v] at this
      exact this.2 j hv
    · rintro ⟨hq, hvv⟩ v
      by_cases hvQ : v ∈ Q
      · exact (e2 ⟨v, hvQ⟩).1 (hq ⟨v, hvQ⟩)
      · rw [hUl β v hvQ, hw (g β) v]
        exact ⟨hJoff κ v hvQ, fun j hvj => congrFun hvv ⟨j, v, hvj⟩⟩
  obtain ⟨Yb, hYf, aY, yb, yG, YQ, yQ, hA1, hA2, hA3, hA4, hA5⟩ :=
    assemble (fun q : Q => ↥(W q.1 q.2)) zQ Kc (fun β q => hWfi β q.1 q.2) wv Hs hH

  have hLbK : ∀ β, (K β).lev.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) J.Lb := fun β => by
    rw [hJLb, ← hH0L]
    refine Eq.trans ?_ ((F u).levJ_Lb h1 (g β))
    ext x
    exact (hRd.lb β x).trans (hR0.lb (g β) x).symm

  have hle : ∀ β, (K β).lev.U ≤ J.U.map (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom := by
    intro β x hx
    have hx' := ((K β).lev.U_eq x).1 hx
    refine ⟨(reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).symm x, (hmemU _).2 ⟨(hUP _).1 (by rw [MulEquiv.apply_symm_apply]; exact hx'.1), fun v => ?_⟩,
      MulEquiv.apply_symm_apply _ _⟩
    have hv' : reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (bc (prV (E := (I.rec7 l Z).host.E) v) ((reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).symm x)) ∈ (K β).lev.Uloc v := by
      rw [← hbc, MulEquiv.apply_symm_apply]; exact hx'.2 v
    by_cases hvQ : v ∈ Q
    · rw [ulocQ_pos H0 Q W hvQ]; exact (hmap v _ _).1 (hWle β v hvQ hv')
    · rw [ulocQ_neg H0 Q W hvQ]
      rw [hUl β v hvQ, hw (g β) v] at hv'
      have h2 := hv'.1
      rw [hH0U v] at h2
      exact (hmap v _ _).1 h2

  have hJg : ∀ (j : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (hv : ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal),
      ∀ x ∈ levelVL (I.rec7 l Z).sp.cm.sig ((I.rec7 l Z).sp.X (B.R.m - 1)).gram v J.Lb,
        x ∈ J.Uloc v ↔ ∃ M ∈ HSym (I.rec7 l Z) (B.R.N (B.R.m - 1)) false v,
          (M : Matrix (Fin (B.R.N (B.R.m - 1))) (Fin (B.R.N (B.R.m - 1))) (kv (I.rec7 l Z).host.F v)) = redJS F u j v hv x := by
    intro j v hv x hx
    rw [hJLb] at hx
    rw [hJUl v, ulocQ_neg H0 Q W (hgQ j v hv)]
    have hx' : reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ x ∈ levelVL (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) v (F u).levJ.Lb := by
      rw [hH0L]; exact (reGL_mem_levelVL _ (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ _ rfl v _ x).2 hx
    have e1 : x ∈ H0.Uloc v ↔ reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ x ∈ (F u).levJ.Uloc v := by rw [hH0U v]; exact (hmap v _ _).symm
    exact e1.trans ((F u).glevJ.mem j v hv _ hx')
  have hJo : ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), v ∉ Q → v ∉ badG (I.rec7 l Z) →
      (J.Uloc v).map (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom = (F u).levJ.Uloc v := by
    intro v hvQ _
    rw [hJUl v, ulocQ_neg H0 Q W hvQ]
    exact (hH0U v).symm

  have hoff : ∀ κ : J.U, ∃ y ∈ (F u).levJ.U, (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) y = 1) ∧
      ∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) y = φ v κ := by
    intro κ
    obtain ⟨y, hy, h1y, h2y⟩ := exists_off (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Q (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ κ.1)
      ((hUP _).2 ((hmemU _).1 κ.2).1)
    refine ⟨y, ((F u).levJ.U_eq y).2 ⟨hy, fun v => ?_⟩, h1y, fun v hv => (h2y v hv).trans (hbc v κ.1)⟩
    by_cases hv : v ∈ Q
    · exact (congrArg (· ∈ (F u).levJ.Uloc v) (h1y v hv)).mpr (one_mem _)
    · exact (congrArg (· ∈ (F u).levJ.Uloc v) ((h2y v hv).trans (hbc v κ.1))).mpr (hJoff κ v hv)
  choose off hoffU hoff1 hoff2 using hoff
  let ψv : ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), (F u).levJ.U →* GL (Fin (B.R.N (B.R.m - 1))) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F) :=
    fun v => (bc (prV (E := (I.rec7 l Z).host.E) v)).comp (F u).levJ.U.subtype
  have htriv : ∀ a : (F u).levJ.U, (∀ v, ψv v a = 1) → (F u).levJ.chi a = 1 := fun a ha => (F u).levJ.chi_triv a (fun v _ => ha v)
  have hoffm : ∀ κ κ' : J.U, (F u).levJ.chi ⟨off (κ * κ'), hoffU _⟩ = (F u).levJ.chi ⟨off κ, hoffU κ⟩ * (F u).levJ.chi ⟨off κ', hoffU κ'⟩ := by
    intro κ κ'
    have h := htriv (⟨off (κ * κ'), hoffU _⟩ * (⟨off κ, hoffU κ⟩ * ⟨off κ', hoffU κ'⟩)⁻¹) (fun v => by
      rw [map_mul (ψv v), map_inv (ψv v), map_mul (ψv v)]
      by_cases hv : v ∈ Q
      · have e1 : ψv v ⟨off (κ * κ'), hoffU _⟩ = 1 := hoff1 _ v hv
        have e2 : ψv v ⟨off κ, hoffU κ⟩ = 1 := hoff1 _ v hv
        have e3 : ψv v ⟨off κ', hoffU κ'⟩ = 1 := hoff1 _ v hv
        rw [e1, e2, e3, mul_one, inv_one, mul_one]
      · have e1 : ψv v ⟨off (κ * κ'), hoffU _⟩ = φ v (κ * κ') := hoff2 _ v hv
        have e2 : ψv v ⟨off κ, hoffU κ⟩ = φ v κ := hoff2 _ v hv
        have e3 : ψv v ⟨off κ', hoffU κ'⟩ = φ v κ' := hoff2 _ v hv
        rw [e1, e2, e3, map_mul (φ v), mul_inv_cancel])
    rw [map_mul, map_inv, mul_inv_eq_one, map_mul] at h
    exact h
  have hoff1' : (F u).levJ.chi ⟨off 1, hoffU 1⟩ = 1 := htriv _ fun v => by
    by_cases hv : v ∈ Q
    · exact hoff1 1 v hv
    · exact (hoff2 1 v hv).trans (map_one (φ v))
  let χoff : J.U →* ℂˣ :=
    { toFun := fun κ => (F u).levJ.chi ⟨off κ, hoffU κ⟩
      map_one' := hoff1'
      map_mul' := hoffm }
  let chiJ : J.U →* ℂˣ := χoff * ψ.comp zQ
  have hchiJ : ∀ β (κ : J.U) (κ' : (K β).lev.U), κ'.1 = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ κ.1 → (K β).lev.chi κ' = chiJ κ := by
    intro β κ κ' h
    have hκ'v : ∀ v, bc (prV (E := (I.rec7 l Z).host.E) v) κ'.1 = φ v κ := fun v => by rw [h]; exact hbc v κ.1
    have hκ'U := ((K β).lev.U_eq _).1 κ'.2
    have hoK : off κ ∈ (K β).lev.U := ((K β).lev.U_eq _).2 ⟨(((F u).levJ.U_eq _).1 (hoffU κ)).1, fun v => by
      by_cases hv : v ∈ Q
      · exact (congrArg (· ∈ (K β).lev.Uloc v) (hoff1 κ v hv)).mpr (one_mem _)
      · exact (congrArg (· ∈ (K β).lev.Uloc v) ((hoff2 κ v hv).trans (hκ'v v).symm)).mpr (hκ'U.2 v)⟩
    have hoC : off κ ∈ ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U :=
      (((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U_eq _).2 ⟨(((F u).levJ.U_eq _).1 (hoffU κ)).1, fun v => by
        by_cases hv : v ∈ Q
        · exact (congrArg (· ∈ ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) (hoff1 κ v hv)).mpr (one_mem _)
        · rw [← hUl β v hv]
          exact (congrArg (· ∈ (K β).lev.Uloc v) ((hoff2 κ v hv).trans (hκ'v v).symm)).mpr (hκ'U.2 v)⟩
    obtain ⟨ψK, hψK⟩ : ∃ ψK : ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), (K β).lev.U →* GL (Fin ((I.rec7 l Z).R.N (B.R.m - 1))) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] (v).adicCompletion (I.rec7 l Z).host.F),
        ∀ v x, ψK v x = bc (prV (E := (I.rec7 l Z).host.E) v) x.1 :=
      ⟨fun v => (bc (prV (E := (I.rec7 l Z).host.E) v)).comp (K β).lev.U.subtype, fun _ _ => rfl⟩
    have hq : ∀ v, ψK v (κ' * ⟨off κ, hoK⟩⁻¹) = ψK v κ' * (ψK v ⟨off κ, hoK⟩)⁻¹ := fun v =>
      (map_mul (ψK v) _ _).trans (congrArg (ψK v κ' * ·) (map_inv (ψK v) _))
    have hq_off : ∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) (κ' * ⟨off κ, hoK⟩⁻¹).1 = 1 := fun v hv => by
      have e2 : ψK v ⟨off κ, hoK⟩ = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (bc (prV (E := (I.rec7 l Z).host.E) v) κ.1) := (hψK v _).trans (hoff2 κ v hv)
      have e3 : ψK v κ' = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (bc (prV (E := (I.rec7 l Z).host.E) v) κ.1) :=
        (hψK v κ').trans ((congrArg (bc (prV (E := (I.rec7 l Z).host.E) v)) h).trans (hbc v κ.1))
      have e4 : ψK v κ' * (ψK v ⟨off κ, hoK⟩)⁻¹ = 1 :=
        (congrArg₂ (fun a b : GL (Fin ((I.rec7 l Z).R.N (B.R.m - 1))) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] (v).adicCompletion (I.rec7 l Z).host.F) => a * b⁻¹) e3 e2).trans (mul_inv_cancel _)
      exact (hψK v _).symm.trans ((hq v).trans e4)
    have hq_Q : ∀ v : Q, reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (zQ κ v).1 = bc (prV (E := (I.rec7 l Z).host.E) v.1) (κ' * ⟨off κ, hoK⟩⁻¹).1 := fun v => by
      have e2 : ψK v.1 ⟨off κ, hoK⟩ = 1 := (hψK v.1 _).trans (hoff1 κ v.1 v.2)
      have e4 : ψK v.1 κ' * (ψK v.1 ⟨off κ, hoK⟩)⁻¹ = ψK v.1 κ' :=
        (congrArg (fun b : GL (Fin ((I.rec7 l Z).R.N (B.R.m - 1))) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] (v.1).adicCompletion (I.rec7 l Z).host.F) => ψK v.1 κ' * b⁻¹) e2).trans ((congrArg (ψK v.1 κ' * ·) inv_one).trans (mul_one _))
      have e : ψK v.1 (κ' * ⟨off κ, hoK⟩⁻¹) = ψK v.1 κ' := (hq v.1).trans e4
      have e5 : reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (zQ κ v).1 = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (bc (prV (E := (I.rec7 l Z).host.E) v.1) κ.1) := congrArg (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _) (hzQ κ v)
      have e6 : ψK v.1 κ' = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (bc (prV (E := (I.rec7 l Z).host.E) v.1) κ.1) :=
        (hψK v.1 κ').trans ((congrArg (bc (prV (E := (I.rec7 l Z).host.E) v.1)) h).trans (hbc v.1 κ.1))
      exact e5.trans (e6.symm.trans (e.symm.trans (hψK v.1 _)))
    calc (K β).lev.chi κ' = (K β).lev.chi ((κ' * ⟨off κ, hoK⟩⁻¹) * ⟨off κ, hoK⟩) := congrArg _ (inv_mul_cancel_right κ' _).symm
      _ = (K β).lev.chi (κ' * ⟨off κ, hoK⟩⁻¹) * (K β).lev.chi ⟨off κ, hoK⟩ := map_mul _ _ _
      _ = ψ (zQ κ) * (F u).levJ.chi ⟨off κ, hoffU κ⟩ := congrArg₂ (· * ·) (hψ β _ (zQ κ) hq_Q hq_off)
        ((hchi β ⟨off κ, hoK⟩ ⟨off κ, hoC⟩ rfl (fun v hv => hoff1 κ v hv)).trans
          ((F u).levJ_chi h1 (g β) ⟨off κ, hoC⟩ ⟨off κ, hoffU κ⟩ rfl))
      _ = chiJ κ := mul_comm _ _
  have hyGs : ∀ (κ : J.U) y (j : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (hv : ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal),
      yG (κ • y) ⟨j, v, hv⟩ = redJS F u j v hv (bc (prV (E := (I.rec7 l Z).host.E) v) κ.1) *ᵥ yG y ⟨j, v, hv⟩ := by
    intro κ y j v hv
    exact congrFun (hA3 κ y) ⟨j, v, hv⟩
  have hyI : ∀ y y', (fun j v hv => yG y ⟨j, v, hv⟩) = (fun (j : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (hv : ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal) => yG y' ⟨j, v, hv⟩) →
      yQ y = yQ y' → y = y' := by
    intro y y' hG hQ'
    refine hA4 y y' (funext fun p => ?_) hQ'
    obtain ⟨j, v, hv⟩ := p
    exact congrFun (congrFun (congrFun hG j) v) hv
  have hyQ : ∀ (κ : J.U) y, (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → yQ (κ • y) = yQ y := by
    intro κ y hκ
    exact hA5 κ y (funext fun q => Subtype.ext ((hzQ κ q).trans (hκ q.1 q.2)))
  exact ⟨{
    levJ := J, Yb := Yb, YbFin := hYf, YbAct := aY, yb := yb, yb_orbit := hA1, lb := hLbK, «le» := hle,
    stab := fun β κ => hA2 β κ, chiJ := chiJ, chiJ_eq := hchiJ, J_g := hJg, J_off := hJo,
    yG := fun y j v hv => yG y ⟨j, v, hv⟩, yG_smul := hyGs,
    YQ := YQ, yQ := yQ, y_inj := hyI, yQ_off := hyQ }⟩

end GlobalTheory.Mem.Col2.TwistLevel
end
