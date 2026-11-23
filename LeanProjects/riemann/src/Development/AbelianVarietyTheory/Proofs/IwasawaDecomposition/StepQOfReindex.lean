import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianClassConditionOfChartClasses
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OpenCongruenceSubgroupPreservesPrincipalLatticeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChartQ

open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem stepQ_of_reindex (hc : CMData F E) (S : HSpace E) {n : ℕ} (h : S.rank = n) {σ : E →ₐ[F] E}
    (hσ : σ = hc.sig) {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ a b, J a b = S.gram (Fin.cast h.symm a) (Fin.cast h.symm b))
    {gp : Fin 2 → ℕ} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (Q : Finset (HeightOneSpectrum (𝓞 F)))
    (K : Formalism.L2.Forms.StepLevel F E σ J T f bad) (H0 : Formalism.L2.Herm.StepLevel hc S gp T f)
    (hQ : ∀ v ∈ Q, ((T : ℕ) : 𝓞 F) ∉ v.asIdeal ∧ ∀ j, ((gp j : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (hLb : K.Lb = reL h H0.Lb) (hU : ∀ v, v ∉ Q → K.Uloc v = (H0.Uloc v).map (reGL h _).toMonoidHom) :
    ∃ L : Formalism.L2.Herm.StepLevelQ hc S gp T f Q, L.Lb = H0.Lb ∧
      (∀ v, K.Uloc v = (L.Uloc v).map (reGL h _).toMonoidHom) ∧ K.U = L.U.map (reGL h _).toMonoidHom := by
  subst h
  subst hσ
  obtain rfl : J = S.gram := by
    ext a b
    simpa using hJ a b
  simp only [GlobalTheory.HermTransport.reL_refl'] at hLb
  simp only [GlobalTheory.HermTransport.reGL_refl_hom', Subgroup.map_id] at hU ⊢
  have hgQ : ∀ (i : Fin 2) v, ((gp i : ℕ) : 𝓞 F) ∈ v.asIdeal → v ∉ Q := fun i v hv hvQ => (hQ v hvQ).2 i hv
  have hTQ : ∀ v, ((T : ℕ) : 𝓞 F) ∈ v.asIdeal → v ∉ Q := fun v hv hvQ => (hQ v hvQ).1 hv
  let L : Formalism.L2.Herm.StepLevelQ hc S gp T f Q :=
    { Lb := H0.Lb
      Lb_fin := H0.Lb_fin
      Lb_span := H0.Lb_span
      Lb_int := H0.Lb_int
      Lb_dual := H0.Lb_dual
      Lb_index := H0.Lb_index
      Uloc := K.Uloc
      Uloc_lev := fun v => hLb ▸ K.Uloc_lev v
      Uloc_hyp := fun v h0 h1 hT hvQ => (hU v hvQ).trans (H0.Uloc_hyp v h0 h1 hT)
      Uloc_g := fun i v hv x hx => (hU v (hgQ i v hv)) ▸ H0.Uloc_g i v hv x hx
      UlocAlt := fun v hv x => (hU v (hTQ v hv)) ▸ H0.UlocAlt v hv x
      Uloc_Q := fun v _ => by
        obtain ⟨N, hN, hx⟩ := GlobalTheory.T.open_congruence_subgroup_preserves_principal_lattice hc.sig S.gram K v
        exact ⟨N, hN, fun x hx' => hx x (hLb ▸ hx'.1) (hLb ▸ hx'.2)⟩
      U := K.U
      U_eq := K.U_eq }
  exact ⟨L, rfl, fun v => rfl, rfl⟩

end Gen

theorem chartTie_toQ : ∀ {D : D7} {T : ℕ} (Q : Finset (HeightOneSpectrum (𝓞 D.host.F))) {i : ℕ} (hm : i ≤ D.R.m) {cl : Type} (st : cl → Type) [∀ c, Group (st c)] (lt : cl → Submodule (𝓞 D.host.E) (D.sp.X i).V) (K : LevelChart D T (badQ D Q) i hm st (fun c => latCrd D i hm (lt c))) (H0 : Formalism.L2.Herm.StepLevel D.sp.cm (D.sp.X i) D.host.g T D.R.f), (∀ v ∈ Q, ((T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal ∧ ∀ j, ((D.host.g j : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) → K.lev.Lb = reL (rankN D i hm) H0.Lb → (∀ v, v ∉ Q → K.lev.Uloc v = (H0.Uloc v).map (reGL (rankN D i hm) _).toMonoidHom) → ∃ (L : Formalism.L2.Herm.StepLevelQ D.sp.cm (D.sp.X i) D.host.g T D.R.f Q) (C : Formalism.L2.Herm.ClassTie D.sp.cm (D.sp.X i) L.Lb L.U st lt), L.Lb = H0.Lb ∧ SameCar (rankN D i hm) L.Lb K.lev.Lb L.Uloc K.lev.Uloc L.U K.lev.U (fun c => (C.y c).1) (fun c => (K.y c).1) (fun c s => (C.stabI c s).1) (fun c s => (K.stabI c s).1) := by
  intro D T Q i hm cl st _ lt K H0 hQ hLb hU
  obtain ⟨L, hL, hUloc, hUU⟩ := GlobalTheory.ChartQ.stepQ_of_reindex D.sp.cm (D.sp.X i) (rankN D i hm) (σ := sigD D) rfl
    (fun a b => rfl) Q K.lev H0 hQ hLb hU
  obtain ⟨C, hy, hst⟩ := GlobalTheory.HermTransport.classTie_of_reindex D.sp.cm (D.sp.X i) (rankN D i hm) rfl (fun a b => rfl)
    (Equiv.refl cl) lt K.y K.y_bij (fun c x => by rw [← GlobalTheory.HermTransport.latCrd_eq_reL]; exact K.y_lat c x) K.stabI
    K.stabI_inj K.stabI_range L.Lb L.U (hL ▸ hLb) hUU
  exact ⟨L, C, hL, ⟨hL ▸ hLb, hUloc, hUU, fun c => hy c, fun c s => hst c s⟩⟩

end GlobalTheory.ChartQ
