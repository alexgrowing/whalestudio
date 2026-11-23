import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.HidaOrdinaryHecke.EigKill
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.HidaOrdinaryHecke.KerSp
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.ClParts
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HiComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SpecIntIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.LocIdem
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

universe u in
private theorem sr_abs {R A K M W ι ι' : Type} [CommRing R] [CommRing A] [Algebra R A] [Field K]
    [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
    [AddCommGroup W] [Module K W] {J : Type u} (Y0 Y : Submodule A M) [Module.Free A Y0] (hle : Y ≤ Y0)
    (op : ι → Module.End A M) [hc : Fact (CommOn Y op)] (s : ι' → ι) (e : Module.End A Y0)
    (hi : IsIdempotentElem e) (hY : ∀ y : Y0, (y : M) ∈ Y ↔ e y = y) (χ : A →+* K) (sp : M → W)
    (hadd : ∀ f ∈ Y0, ∀ f' ∈ Y0, sp (f + f') = sp f + sp f') (hsmul : ∀ f ∈ Y0, ∀ b : A, sp (b • f) = χ b • sp f)
    (hind : ∀ (κ : Type) (b : Module.Basis κ A Y0), LinearIndependent K fun i => sp (b i))
    (opC : ι → Module.End K W) (hop : ∀ i, ∀ f ∈ Y0, sp (op i f) = opC i (sp f))
    (Z : J → Submodule K W) (hZ : ∀ j i, ∃ μ : K, ∀ F ∈ Z j, opC (s i) F = μ • F)
    (hOZ : ∀ f ∈ Y0, sp f ∈ ⨆ j, Z j) (I : Ideal A) (hI : I = RingHom.ker χ)
    (t : heckeAlg Y op) (ht : t ∈ Algebra.adjoin R (Set.range fun i => heckeGen Y op (s i))) (k : ℕ)
    (h : ∀ y : Y, ((t ^ k : heckeAlg Y op) : Module.End A Y) y ∈ (I • ⊤ : Submodule A Y)) (y : Y) :
    (t : Module.End A Y) y ∈ (I • ⊤ : Submodule A Y) := by
  subst hI
  have hk := UpperTheory.V.Th.AnnihilatorQuotientFinite.kerSp Y0 Y e hi hle hY χ sp hadd hsmul hind
  have key : ∃ φ : Module.End K W, (∀ f : Y, sp ((t : Module.End A Y) f : Y) = φ (sp f)) ∧
      ∀ j, ∃ μ : K, ∀ F ∈ Z j, φ F = μ • F := by
    clear h
    induction ht using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨opC (s i), fun f => hop _ _ (hle f.2), fun j => hZ j i⟩
    | algebraMap r =>
      refine ⟨algebraMap K _ (χ (algebraMap R A r)), fun f => ?_, fun j => ⟨_, fun F _ => rfl⟩⟩
      rw [IsScalarTower.algebraMap_apply R A (heckeAlg Y op)]
      exact hsmul _ (hle f.2) _
    | add a b _ _ ha hb =>
      obtain ⟨φ, h1, h2⟩ := ha
      obtain ⟨ψ, h3, h4⟩ := hb
      refine ⟨φ + ψ, fun f => ?_, fun j => ?_⟩
      · rw [LinearMap.add_apply, ← h1, ← h3]
        exact hadd _ (hle (Subtype.prop _)) _ (hle (Subtype.prop _))
      · obtain ⟨μ, hμ⟩ := h2 j
        obtain ⟨ν, hν⟩ := h4 j
        exact ⟨μ + ν, fun F hF => by rw [LinearMap.add_apply, hμ F hF, hν F hF, add_smul]⟩
    | mul a b _ _ ha hb =>
      obtain ⟨φ, h1, h2⟩ := ha
      obtain ⟨ψ, h3, h4⟩ := hb
      refine ⟨φ * ψ, fun f => ?_, fun j => ?_⟩
      · rw [Module.End.mul_apply, ← h3, ← h1]
        rfl
      · obtain ⟨μ, hμ⟩ := h2 j
        obtain ⟨ν, hν⟩ := h4 j
        exact ⟨ν * μ, fun F hF => by rw [Module.End.mul_apply, hν F hF, map_smul, hμ F hF, smul_smul]⟩
  obtain ⟨φ, h1, h2⟩ := key
  have hp : ∀ (m : ℕ) (f : Y), sp (((t ^ m : heckeAlg Y op) : Module.End A Y) f : Y) = (φ ^ m) (sp f) := by
    intro m
    induction m with
    | zero => intro f; rw [pow_zero, pow_zero]; rfl
    | succ m ih =>
      intro f
      rw [pow_succ, pow_succ, Module.End.mul_apply, ← h1, ← ih]
      rfl
  rw [← hk, h1]
  refine UpperTheory.V.Th.AnnihilatorQuotientFinite.eigKill φ k _ ?_ (by rw [← hp]; exact (hk _).2 (h y))
  refine (iSup_le fun j => ?_ : ⨆ j, Z j ≤ _) (hOZ _ (hle y.2))
  obtain ⟨μ, hμ⟩ := h2 j
  exact fun F hF => Submodule.mem_iSup_of_mem μ (Module.End.mem_eigenspace_iff.2 (hμ F hF))
attribute [local instance 2000] UpperTheory.V.W.coefLocal
attribute [-instance] GlobalTheory.AdmLoc.modFun

set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Th.AnnihilatorQuotientFinite.sphRed :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop), H.Aut ι P →
    ∀ (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n), lam ∈ H.admitted → H.Arith θ x.toRingHom lam → ∀ (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))],
    ∀ t ∈ Algebra.adjoin c.O (Set.range fun p : H.Wp × Fin n => H.gen θ a K (.inl p)), ∀ k : ℕ,
    (∀ y : H.MK θ a K, ((t ^ k : H.TK θ a K) : Module.End A (H.MK θ a K)) y ∈ (RingHom.ker x • ⊤ : Submodule A (H.MK θ a K))) → ∀ y : H.MK θ a K, (t : Module.End A (H.MK θ a K)) y ∈ (RingHom.ker x • ⊤ : Submodule A (H.MK θ a K)) := by
  intro L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι P hP x lam hlam har a K _ t ht k h y
  haveI : Finite (ResidueField c.O) := (UpperTheory.V.abelian₂.dvr_finite l c.O).2.1
  haveI : IsCNL A := IsCNL.ofCO c.O A
  obtain ⟨h0, hfin, hfree, -⟩ := hiComm L Ω l n c H hH A θ hθ K
  obtain ⟨e, -, hi, hY, -⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locIdem A _ _ _ (H.op A) (fun i => algebraMap c.O A (a i)) h0
  obtain ⟨d, ξ, c0, sp, hsp⟩ := spec L Ω l n c H hH A θ hθ ι x lam har
  have hO := (clParts L Ω l n c H hH A θ hθ ι P hP x lam d ξ c0 sp hsp hlam K c0 le_rfl).2
  have hOZ : ∀ f ∈ H.X.Ord (H.τA A) θ (H.lev K), sp f ∈ ⨆ Y : {Y : H.Part ι lam ξ // P lam Y.r}, Y.1.Y := fun f hf => by
    have h1 : sp f ∈ H.OrdAt θ ι x.toRingHom lam ξ K c0 := hsp.span K c0 le_rfl ▸ Submodule.subset_span ⟨f, hf, rfl⟩
    exact (hO.le.trans (iSup_mono fun _ => inf_le_left)) h1
  have hI : RingHom.ker x = RingHom.ker (ι.toRingHom.comp x.toRingHom) := by
    ext b
    simp [RingHom.mem_ker]
  exact sr_abs (R := c.O) (H.X.Ord (H.τA A) θ (H.lev K)) (H.MK θ a K) inf_le_left (H.op A) Sum.inl e hi hY
    (ι.toRingHom.comp x.toRingHom) sp (hsp.add K) (hsp.smul K) (hsp.indep K) (H.opC ι lam d) (hsp.op K)
    (fun Y : {Y : H.Part ι lam ξ // P lam Y.r} => Y.1.Y) (fun Y i => ⟨_, Y.1.sph i.1 _⟩) hOZ _ hI t ht k h y
