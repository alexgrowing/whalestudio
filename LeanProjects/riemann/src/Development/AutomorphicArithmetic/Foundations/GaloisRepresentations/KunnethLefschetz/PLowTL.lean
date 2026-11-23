import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
import Development.EtaleCohomology.EtaleTrace.TorsionH0PointOfTwistCoverCocycle
import Development.EtaleCohomology.EtaleTrace.PtCoverPf
import Development.EtaleCohomology.EtaleTrace.TwZeroPfSplit
import Development.EtaleCohomology.EtaleTrace.PrimSplitPf
import Development.EtaleCohomology.EtaleTrace.CocEqPf
import Development.EtaleCohomology.EtaleTrace.EtaleTateTwistSectionConstantOnPointsOfConnected
import Development.EtaleCohomology.EtaleTrace.PtCovPf
import Development.EtaleCohomology.EtaleTrace.TateTwistSectionConstantOnPointsOfTwLocPtCov
import Development.EtaleCohomology.TateTwists.TwLocPfR
import Development.EtaleCohomology.TateTwists.TwSecLocPfZarR
import Development.EtaleCohomology.TateTwists.AlgPowPfR
import Development.EtaleCohomology.TateTwists.TwTorsPfR

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace CochainComplex.HomComplex

namespace UpperTheory.Gal.KunnethLefschetz

private theorem twLoc : LateralTheory.EtaleFoundations.CongruenceLocalDecomposition.TwLoc :=
  LateralTheory.EtaleFoundations.TwLocPf.TwLoc_of
    (LateralTheory.EtaleFoundations.TwSecLocPf.TwSecLoc_of_alg LateralTheory.EtaleFoundations.AlgPowPf.AlgPow_of)
    LateralTheory.EtaleFoundations.TwTorsPf.TwTors_of

private theorem twZero : TwZero := TwZero_of_split twLoc PrimSplit_of

private theorem lowSec : EtaleTateTwistSectionsDeterminedByPointsOfProper := tateTwistSections_determinedByPoints_of_constant twLoc PtCov_of (tateTwistSection_constantOnPoints_of_twLoc_ptCov twLoc PtCov_of)

private theorem exists_ofRings_sec_eq_twF_zero (k : Type) [Field k] [IsAlgClosed k] (q : ℕ) (s : Sec (tw q 0) (S k)) :
    ∃ t, ofRings.sec (twF q 0) (S k) t = s := by
  have h := Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)) s
  obtain ⟨t, ht⟩ := PtCover_of k _ h
  refine ⟨t, ht.trans ?_⟩
  simp
  rfl

private theorem ofRings_sec_twF_zero_injective (k : Type) [Field k] [IsAlgClosed k] (q : ℕ)
    (t1 t2 : ToType ((Scheme.Γ ⋙ twF q 0).obj (Opposite.op (S k))))
    (h : ofRings.sec (twF q 0) (S k) t1 = ofRings.sec (twF q 0) (S k) t2) : t1 = t2 := by
  have h2 := Presheaf.equalizerSieve_mem Scheme.etaleTopology
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)) t1 t2 h
  have h3 := PtCover_of k _ h2
  have h4 : (Scheme.Γ ⋙ twF q 0).map (𝟙 (Opposite.op (S k))) t1 =
      (Scheme.Γ ⋙ twF q 0).map (𝟙 (Opposite.op (S k))) t2 := h3
  rwa [CategoryTheory.Functor.map_id, ModuleCat.id_apply, ModuleCat.id_apply] at h4

private theorem res_twGen_zero_eq_twGen_prim_map {q : ℕ} {U V : Scheme.{0}} (x : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res x (twGen 0 ζ) = twGen 0 (Prim.map (Scheme.Γ.map x.op).hom ζ) := by
  have hn := congrArg (fun φ => (ModuleCat.Hom.hom φ)
    (Submodule.Quotient.mk (Finsupp.single ζ 1) : (Scheme.Γ ⋙ twF q 0).obj (Opposite.op U)))
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)).naturality x.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hn
  refine hn.symm.trans ?_
  refine congrArg (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)).app (Opposite.op V))) ?_
  exact congrArg Submodule.Quotient.mk Finsupp.mapDomain_single

private theorem exists_nsmul_eq_of_single_one_eq {q : ℕ} [NeZero q] {P N : Type*} [AddCommGroup N] [Module (ULift.{1, 0} (ZMod q)) N]
    (φ : (P →₀ ULift.{1, 0} (ZMod q)) →ₗ[ULift.{1, 0} (ZMod q)] N) (g0 : N)
    (h : ∀ ξ, φ (Finsupp.single ξ 1) = g0) (f : P →₀ ULift.{1, 0} (ZMod q)) :
    ∃ n : ℕ, φ f = n • g0 := by
  induction f using Finsupp.induction with
  | zero => exact ⟨0, by simp⟩
  | single_add ξ c g _ _ ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨c.down.val + n, ?_⟩
    have hc : c = ((c.down.val : ℕ) : ULift.{1, 0} (ZMod q)) := by
      apply ULift.ext
      rw [ULift.down_natCast, ZMod.natCast_zmod_val]
    calc φ (Finsupp.single ξ c + g) = c • g0 + n • g0 := by
          rw [map_add, ← Finsupp.smul_single_one, map_smul, h, hn]
      _ = (c.down.val + n) • g0 := by
          rw [add_nsmul, ← Nat.cast_smul_eq_nsmul (ULift.{1, 0} (ZMod q)) c.down.val, ← hc]

private theorem sec_res_sec_map_comm {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (k : V ⟶ U)
    (b : Sec F U) : Sec.res k (Sec.map φ b) = Sec.map φ (Sec.res k b) := by
  simp only [Sec.res, Sec.map]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.hom.naturality]

private theorem lowPt (hA : A9) (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k] (hl : (l : k) ≠ 0) (j : ℕ) :
    (∀ z : Ht (l ^ j) (sch.obj (S k)) 0 0, ∃ a : ℕ, z = a • one (l ^ j) (sch.obj (S k))) ∧
      ∀ a : ℕ, a • one (l ^ j) (sch.obj (S k)) = 0 → l ^ j ∣ a := by
  haveI : NeZero (l ^ j) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨_, e, _, he2⟩ := hA (ZMod (l ^ j)) (tw (l ^ j) 0)
  obtain ⟨ζ0⟩ := exists_prim l k hl j
  let φ : ((Prim (l ^ j) Γ(S k, ⊤)) →₀ ULift.{1, 0} (ZMod (l ^ j))) →ₗ[ULift.{1, 0} (ZMod (l ^ j))]
      Sec (tw (l ^ j) 0) (S k) :=
    (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF (l ^ j) 0)).app
      (Opposite.op (S k)))).comp (twRel (l ^ j) 0 Γ(S k, ⊤)).mkQ
  have hone : one (l ^ j) (sch.obj (S k)) = e (S k) (twGen 0 ζ0) := by
    obtain ⟨α, hα, hev⟩ := he2 (S k) (twGen 0 ζ0)
    have hnat : ∀ (U : Scheme.{0}) (x : Sx (sch.obj (S k)) 0 U) (ζ : Prim (l ^ j) Γ(U, ⊤)),
        ev (α : Cochain _ _ 0) 0 0 (by simp) U x = resGen 0 ζ := by
      intro U x ζ
      rw [evNat (ZMod (l ^ j)) (tw (l ^ j) 0) (S k) U (α : Cochain _ _ 0) x, hev]
      refine (sec_res_sec_map_comm (resι (ZMod (l ^ j)) (tw (l ^ j) 0)) (x : U ⟶ S k) (twGen 0 ζ0)).trans ?_
      exact congrArg (Sec.map (resι (ZMod (l ^ j)) (tw (l ^ j) 0)))
        ((res_twGen_zero_eq_twGen_prim_map (x : U ⟶ S k) ζ0).trans (twZero (l ^ j) U _ ζ))
    have h1 := pick_spec (show ∃ c, (fun c => ∃ β : Cocycle ((chains (ZMod (l ^ j))).obj (sch.obj (S k)))
        (res (ZMod (l ^ j)) (tw (l ^ j) 0)) 0, CohomologyClass.mk β = c ∧
          ∀ (U : Scheme) (x : Sx (sch.obj (S k)) 0 U) (ζ : Prim (l ^ j) Γ(U, ⊤)),
            ev (β : Cochain _ _ 0) 0 0 (by simp) U x = resGen 0 ζ) c from ⟨_, α, hα, hnat⟩)
    obtain ⟨β, hβ, hβev⟩ := h1
    refine hβ.symm.trans ((congrArg CohomologyClass.mk (CocEq_of _ _ _ β α (fun U x => ?_))).trans hα)
    exact (hβev U x (Prim.map (Scheme.Γ.map x.op).hom ζ0)).trans (hnat U x _).symm
  refine ⟨fun z => ?_, fun a ha => ?_⟩
  · obtain ⟨t, ht⟩ := exists_ofRings_sec_eq_twF_zero k (l ^ j) ((e (S k)).symm z)
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (twRel (l ^ j) 0 Γ(S k, ⊤)) t
    obtain ⟨n, hn⟩ := exists_nsmul_eq_of_single_one_eq φ (twGen 0 ζ0)
      (fun ξ => (show φ (Finsupp.single ξ 1) = twGen 0 ζ0 from twZero (l ^ j) (S k) ξ ζ0)) f
    refine ⟨n, ?_⟩
    have hf : φ f = (e (S k)).symm z := ht
    rw [hone, ← map_nsmul, ← hn, hf, AddEquiv.apply_symm_apply]
  · rw [hone, ← map_nsmul] at ha
    have hs : a • twGen 0 ζ0 = (0 : Sec (tw (l ^ j) 0) (S k)) :=
      (e (S k)).injective (ha.trans (map_zero _).symm)
    have h3 : (Submodule.Quotient.mk (a • Finsupp.single ζ0 (1 : ULift.{1, 0} (ZMod (l ^ j)))) :
        (_ ⧸ twRel (l ^ j) 0 Γ(S k, ⊤))) = Submodule.Quotient.mk 0 :=
      ofRings_sec_twF_zero_injective k (l ^ j) _ _ (show φ (a • Finsupp.single ζ0 1) = φ 0 by
        rw [map_nsmul, map_zero]
        exact hs)
    have h4 := (Submodule.Quotient.mk_eq_zero _).1 (h3.trans (Submodule.Quotient.mk_zero _))
    let ψ := Finsupp.linearCombination (ULift.{1, 0} (ZMod (l ^ j)))
      (fun _ : Prim (l ^ j) Γ(S k, ⊤) => (1 : ULift.{1, 0} (ZMod (l ^ j))))
    have hker : twRel (l ^ j) 0 Γ(S k, ⊤) ≤ LinearMap.ker ψ := by
      rw [twRel, Submodule.span_le]
      rintro x ⟨ζ, ξ, b, -, rfl⟩
      simp [ψ]
      exact sub_self (1 : ULift.{1, 0} (ZMod (l ^ j)))
    have h5 : ψ (a • Finsupp.single ζ0 1) = 0 := hker h4
    have h6 : ((a : ZMod (l ^ j))) = 0 := by
      have := congrArg ULift.down h5
      simpa [ψ] using this
    exact (ZMod.natCast_eq_zero_iff a (l ^ j)).1 h6

theorem lowTL_holds : LowTL := by
  intro hIn l _ k _ _ hl j
  obtain ⟨_, e, he1, _⟩ := (In.a9 hIn) (ZMod (l ^ j)) (tw (l ^ j) 0)
  refine ⟨lowPt (In.a9 hIn) l k hl j, ?_⟩
  intro X p hp z
  have hz : ∀ y : Pt p, pull (ZMod (l ^ j)) (sch.map y.1) (tw (l ^ j) 0) 0 z =
      e (S k) (Sec.res y.1 ((e X).symm z)) := by
    intro y
    rw [← he1, AddEquiv.apply_symm_apply]
  obtain ⟨h1, h2⟩ := lowSec l k hl j p hp ((e X).symm z)
  refine ⟨fun hy => ?_, fun hc y y' => ?_⟩
  · have h0 : (e X).symm z = 0 :=
      h1 (fun y => (e (S k)).injective (by rw [← hz, hy y, map_zero]))
    have := congrArg (e X) h0
    rwa [AddEquiv.apply_symm_apply, map_zero] at this
  · rw [hz, hz, h2 hc y y']

end UpperTheory.Gal.KunnethLefschetz
