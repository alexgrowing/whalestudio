import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.SwapN

open GlobalTheory.Mem.Top.TypesTrue

theorem heq_apply_cast {X : Type*} {P P' : Fin 2 → Type} (h : P = P') {a : ∀ k, P k → X} {a' : ∀ k, P' k → X}
    (ha : HEq a a') (k : Fin 2) (v : P k) : a' k (cast (congrFun h k) v) = a k v := by
  subst h
  obtain rfl := eq_of_heq ha
  rfl

theorem cen_transport {r : ℕ} {g : Fin 2 → ℕ} {P P' : Fin 2 → Type} (h : P = P') {ι : Type*} {E : ι → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
    {c : ∀ i, Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P k), GL (Fin r) (ZMod (g kv.1)))) →ₐ[ℂ]
      Module.End ℂ (E i)}
    {c' : ∀ i, Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P' k), GL (Fin r) (ZMod (g kv.1)))) →ₐ[ℂ]
      Module.End ℂ (E i)}
    (hc : HEq c c')
    (e : (∀ kv : (Σ k : Fin 2, P k), GL (Fin r) (ZMod (g kv.1))) ≃* (∀ kv : (Σ k : Fin 2, P' k), GL (Fin r) (ZMod (g kv.1))))
    (he : ∀ x k v, e x ⟨k, cast (congrFun h k) v⟩ = x ⟨k, v⟩) (i : ι) (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P k), GL (Fin r) (ZMod (g kv.1)))))
    (z₁ : Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P' k), GL (Fin r) (ZMod (g kv.1))))) (hz : ∀ x, (z₁ : MonoidAlgebra ℂ _).coeff (e x) =
      (z : MonoidAlgebra ℂ _).coeff x) : c i z = c' i z₁ := by
  subst h
  obtain rfl := eq_of_heq hc
  have he' : ∀ x, e x = x := fun x => funext fun kv => he x kv.1 kv.2
  congr 1
  apply Subtype.ext
  apply MonoidAlgebra.coeff_injective
  refine Finsupp.ext fun x => ?_
  have := hz x
  rw [he'] at this
  exact this.symm

theorem cen_transport₂ {r : ℕ} {g : Fin 2 → ℕ} {P P' : Fin 2 → Type} (h : P = P') {ι κ : Type*} {E : ι → κ → Type*}
    [∀ i j, AddCommGroup (E i j)] [∀ i j, Module ℂ (E i j)]
    {c : ∀ i j, Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P k), GL (Fin r) (ZMod (g kv.1)))) →ₐ[ℂ]
      Module.End ℂ (E i j)}
    {c' : ∀ i j, Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P' k), GL (Fin r) (ZMod (g kv.1)))) →ₐ[ℂ]
      Module.End ℂ (E i j)}
    (hc : HEq c c')
    (e : (∀ kv : (Σ k : Fin 2, P k), GL (Fin r) (ZMod (g kv.1))) ≃* (∀ kv : (Σ k : Fin 2, P' k), GL (Fin r) (ZMod (g kv.1))))
    (he : ∀ x k v, e x ⟨k, cast (congrFun h k) v⟩ = x ⟨k, v⟩) (i : ι) (j : κ) (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P k), GL (Fin r) (ZMod (g kv.1)))))
    (z₁ : Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P' k), GL (Fin r) (ZMod (g kv.1))))) (hz : ∀ x, (z₁ : MonoidAlgebra ℂ _).coeff (e x) =
      (z : MonoidAlgebra ℂ _).coeff x) : c i j z = c' i j z₁ := by
  subst h
  obtain rfl := eq_of_heq hc
  have he' : ∀ x, e x = x := fun x => funext fun kv => he x kv.1 kv.2
  congr 1
  apply Subtype.ext
  apply MonoidAlgebra.coeff_injective
  refine Finsupp.ext fun x => ?_
  have := hz x
  rw [he'] at this
  exact this.symm

theorem mem_center_map {G G' : Type*} [Monoid G] [Monoid G'] (φ : MonoidAlgebra ℂ G ≃ₐ[ℂ] MonoidAlgebra ℂ G')
    {a : MonoidAlgebra ℂ G} (ha : a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G)) : φ a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G') := by
  rw [Subalgebra.mem_center_iff] at ha ⊢
  intro b
  obtain ⟨b, rfl⟩ := φ.surjective b
  rw [← map_mul, ← map_mul, ha b]

end GlobalTheory.Mem.R3.Rw.SwapN

namespace GlobalTheory.Mem.R3.Rw.SwapN

theorem fits_swap : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : NStage B w.C (P.q.W x.o.η x.o.hη)), GrpTrue N f → N.nd.PlG = x.o.N.nd.PlG → HEq N.naut.plGw x.o.N.naut.plGw → HEq N.ntypes.cenAmb x.o.N.ntypes.cenAmb → HEq N.ntypes.cenMt x.o.N.ntypes.cenMt → GrpAt (w.st (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) w.I ∧ ∀ eR, StdIso (w.st (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) w.px eR → CenIs P.q.p N eR := by
  intro K B f T w P x N hG hP hw hA hM
  have hG' : GrpTrue x.o.N f := x.fits.grp
  obtain ⟨⟨plg, hplg⟩, hidem, hcen⟩ := x.fits.grpAt
  let e := grpEquiv N.naut x.o.N.naut
  have hco : ∀ g, x.o.N.ntypes.e0.coeff (e g) = N.ntypes.e0.coeff g := GrpTrue.typeIdempotent_coeff_across_layers hG hG'
  let φ := MonoidAlgebra.domCongr ℂ ℂ e
  have hφ : ∀ (a : MonoidAlgebra ℂ (G0g N.nd)) g, (φ a).coeff (e g) = a.coeff g := by
    intro a g
    simp [φ]
  have he0 : N.ntypes.e0 = φ.symm x.o.N.ntypes.e0 := by
    apply MonoidAlgebra.coeff_injective
    refine Finsupp.ext fun g => ?_
    show _ = (MonoidAlgebra.domCongr ℂ ℂ e.symm x.o.N.ntypes.e0).coeff g
    rw [MonoidAlgebra.coeff_domCongr, MulEquiv.symm_symm, hco]
  have hpe : ∀ k v, plEquiv N.naut x.o.N.naut k v = cast (congrFun hP k) v := by
    intro k v
    show (plF x.o.N.naut k).symm (plF N.naut k v) = _
    rw [Equiv.symm_apply_eq]
    apply Subtype.ext
    rw [plF_apply, plF_apply, heq_apply_cast hP hw k v]
  have he : ∀ (g : G0g N.nd) k v, e g ⟨k, cast (congrFun hP k) v⟩ = g ⟨k, v⟩ := by
    intro g k v
    rw [grpEquiv_apply, ← hpe, Equiv.symm_apply_apply]
  refine ⟨⟨⟨(Equiv.sigmaCongrRight fun k => plEquiv N.naut x.o.N.naut k).trans plg, fun kv => ?_⟩, ?_, ?_⟩, ?_⟩
  · obtain ⟨h1, h2⟩ := hplg ⟨kv.1, plEquiv N.naut x.o.N.naut kv.1 kv.2⟩
    refine ⟨?_, h2⟩
    exact h1.trans (TypesTrue.plGw_plEquiv hG hG' kv.1 kv.2)
  · show IsIdempotentElem N.ntypes.e0
    rw [he0]
    exact hidem.map φ.symm
  · show N.ntypes.e0 ∈ _
    rw [he0]
    exact mem_center_map φ.symm hcen
  · rintro eR ⟨plg1, iso1, hpl1, hact1⟩
    have hstd : StdIso (w.st x.o.Z) w.px (eR.trans e) := by
      refine ⟨(Equiv.sigmaCongrRight fun k => (plEquiv N.naut x.o.N.naut k).symm).trans plg1,
        fun kv => iso1 ⟨kv.1, (plEquiv N.naut x.o.N.naut kv.1).symm kv.2⟩, fun kv => ?_, fun g kv => ?_⟩
      · refine (hpl1 ⟨kv.1, (plEquiv N.naut x.o.N.naut kv.1).symm kv.2⟩).trans ?_
        have := TypesTrue.plGw_plEquiv hG hG' kv.1 ((plEquiv N.naut x.o.N.naut kv.1).symm kv.2)
        exact ((congrArg (x.o.N.naut.plGw kv.1) (Equiv.apply_symm_apply (plEquiv N.naut x.o.N.naut kv.1) kv.2)).symm.trans
          this).symm
      · exact hact1 g _
    have hc := x.fits.cen _ hstd
    have hz1 : ∀ (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g N.nd))), φ (z : MonoidAlgebra ℂ (G0g N.nd)) ∈
        Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g x.o.N.nd)) := fun z => mem_center_map φ z.2
    refine ⟨fun μ z z' hz xx => ?_, fun μ j z z' hz xx => ?_⟩
    · have h1 := hc.amb μ ⟨_, hz1 z⟩ z' (fun g => by
        show _ = (φ (z : MonoidAlgebra ℂ (G0g N.nd))).coeff (e (eR g))
        exact (hz g).trans (hφ _ _).symm) xx
      rw [cen_transport hP hA e he μ z ⟨_, hz1 z⟩ (fun g => hφ _ g)]
      exact h1
    · have h1 := hc.mt μ j ⟨_, hz1 z⟩ z' (fun g => by
        show _ = (φ (z : MonoidAlgebra ℂ (G0g N.nd))).coeff (e (eR g))
        exact (hz g).trans (hφ _ _).symm) xx
      rw [cen_transport₂ hP hM e he μ j z ⟨_, hz1 z⟩ (fun g => hφ _ g)]
      exact h1

end GlobalTheory.Mem.R3.Rw.SwapN
