import Development.EtaleCohomology.TateTwists.StrictHenselianAcyclic

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite TensorProduct GlobalTheory.EtC GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec

namespace LateralTheory.EtaleFoundations.TwLocPf

theorem ofRings_sec_res {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) {V U : Scheme.{0}}
    (g : V ⟶ U) (x : M.obj Γ(U, ⊤)) :
    Sec.res g (ofRings.sec M U x) = ofRings.sec M V ((M.map g.appTop).hom x) := by
  have h := congrArg (fun f => f.hom x)
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality g.op)
  simp only [ModuleCat.hom_comp] at h
  exact h.symm

theorem twGen_res (q : ℕ) (i : ℤ) (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom) := by
  refine (ofRings_sec_res (twF q i) g _).trans ?_
  unfold twGen
  congr 1
  change Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map g.appTop.hom) (Finsupp.single ζ 1)) = _
  rw [Finsupp.mapDomain_single]

def TwSecLoc : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (y : Sec (tw q i) U),
  Loc U fun V g => ∃ c : ℕ, Sec.res g y = c • twGen i (ζ.map g.appTop.hom)

def TwTors : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) (U : Scheme.{0}) [Nonempty U] (ζ : Prim q Γ(U, ⊤)) (c : ℕ),
  c • twGen i ζ = 0 → q ∣ c

theorem TwLoc_of (h1 : TwSecLoc) (h2 : TwTors) : LateralTheory.EtaleFoundations.CongruenceLocalDecomposition.TwLoc := by
  intro q _ i
  exact ⟨fun U ζ y => h1 q i U ζ y, fun U _ ζ c hc => h2 q i U ζ c hc, fun V U g ζ => twGen_res q i V U g ζ⟩

end LateralTheory.EtaleFoundations.TwLocPf
