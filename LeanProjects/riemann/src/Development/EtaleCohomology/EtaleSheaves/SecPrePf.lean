import Development.EtaleCohomology.EtaleSheaves.SHEqvPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC Opposite

namespace LateralTheory.E.SecPrePf
open LateralTheory.E.t_E3Cut

theorem id_mem (hSec : SHSection) (A : CommRingCat.{0}) (hA : SH A) {S : Sieve (Spec A)}
    (hS : S ∈ Scheme.etaleTopology (Spec A)) : S.arrows (𝟙 _) := by
  obtain ⟨𝒰, hle⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hS
  have : IsLocalRing A := hA.elim fun h _ => h.toIsLocalRing
  obtain ⟨hcov, -⟩ := (Scheme.presieve₀_mem_precoverage_iff _).1 𝒰.mem₀
  obtain ⟨j, y, hy⟩ := hcov (IsLocalRing.closedPoint A : PrimeSpectrum A)
  have : Etale (𝒰.f j) := 𝒰.map_prop j
  have hsurj : Function.Surjective (𝒰.f j) := by
    intro z
    have hopen : IsOpen (Set.range (𝒰.f j)) := (𝒰.f j).isOpenMap.isOpen_range
    have hmem : (IsLocalRing.closedPoint A : PrimeSpectrum A) ∈ Set.range (𝒰.f j) := ⟨y, hy⟩
    exact (IsLocalRing.specializes_closedPoint (z : PrimeSpectrum A)).mem_open hopen hmem
  have : Surjective (𝒰.f j) := ⟨hsurj⟩
  obtain ⟨s, hs⟩ := hSec A hA (𝒰.f j)
  have h1 : S.arrows (𝒰.f j) := hle _ _ (Presieve.ofArrows.mk j)
  have h2 := S.downward_closed h1 s
  rwa [hs] at h2

theorem mem_of_cov (hSec : SHSection) (A : CommRingCat.{0}) (hA : SH A) {V : Scheme.{0}} (h : Spec A ⟶ V)
    (S : Sieve V) (hS : S ∈ Scheme.etaleTopology V) : S.arrows h := by
  have := id_mem hSec A hA (Scheme.etaleTopology.pullback_stable h hS)
  simpa using this

variable {R : Type} [CommRing R]

@[simps]
def sky (U : Scheme.{0}) (N : ModuleCat.{1} (ULift.{1} R)) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj V := ModuleCat.of _ ((U ⟶ V.unop) → N)
  map g := ModuleCat.ofHom
    { toFun := fun φ h => φ (h ≫ g.unop)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_id _ := by ext; simp
  map_comp _ _ := by ext; simp

theorem sky_isSheaf (U : Scheme.{0})
    (hU : ∀ {V : Scheme.{0}} (h : U ⟶ V) (S : Sieve V), S ∈ Scheme.etaleTopology V → S.arrows h)
    (N : ModuleCat.{1} (ULift.{1} R)) : Presheaf.IsSheaf Scheme.etaleTopology (sky U N) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget (s := forget (ModuleCat.{1} (ULift.{1} R))),
    isSheaf_iff_isSheaf_of_type]
  intro V S hS x hx
  have hc := hx.to_sieveCompatible
  refine ⟨fun h => x h (hU h S hS) (𝟙 U), ?_, ?_⟩
  · intro W f hf
    funext k
    have e := congrFun (hc f k hf) (𝟙 U)
    change x (k ≫ f) _ (𝟙 U) = x f hf k
    rw [e]
    change x f hf (𝟙 U ≫ k) = _
    rw [Category.id_comp]
  · intro t ht
    funext h
    have e := congrFun (ht h (hU h S hS)) (𝟙 U)
    change t (𝟙 U ≫ h) = _ at e
    rw [Category.id_comp] at e
    exact e

@[simps]
def toSky (Q : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0}) {N : ModuleCat.{1} (ULift.{1} R)}
    (g : Q.obj (op U) ⟶ N) : Q ⟶ sky U N where
  app V := ModuleCat.ofHom
    { toFun := fun p h => g.hom ((Q.map h.op).hom p)
      map_add' := fun _ _ => by funext h; simp
      map_smul' := fun _ _ => by funext h; simp }
  naturality V W f := by
    ext p
    funext h
    change g.hom ((Q.map h.op).hom ((Q.map f).hom p)) = g.hom ((Q.map (h ≫ f.unop).op).hom p)
    rw [op_comp, Quiver.Hom.op_unop, Q.map_comp]
    rfl

theorem toSheafify_bij (U : Scheme.{0})
    (hU : ∀ {V : Scheme.{0}} (h : U ⟶ V) (S : Sieve V), S ∈ Scheme.etaleTopology V → S.arrows h)
    (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) :
    Function.Bijective ((toSheafify Scheme.etaleTopology P).app (op U)).hom := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have e := toSheafify_sheafifyLift Scheme.etaleTopology (toSky P U (𝟙 _)) (sky_isSheaf U hU _)
    have e2 := congrFun (congrArg (fun φ => (φ.app (op U)).hom x) e) (𝟙 U)
    simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply, hx, map_zero] at e2
    have e3 : (P.map (𝟙 U).op).hom x = 0 := e2.symm
    rwa [op_id, P.map_id] at e3
  · intro y
    let η := toSheafify Scheme.etaleTopology P
    let Q := sheafify Scheme.etaleTopology P
    let g : Q.obj (op U) ⟶ ModuleCat.of _ (Q.obj (op U) ⧸ LinearMap.range (η.app (op U)).hom) :=
      ModuleCat.ofHom (Submodule.mkQ _)
    have e := sheafify_hom_ext Scheme.etaleTopology (toSky Q U g) 0 (sky_isSheaf U hU _) (by
      ext V p
      funext h
      have nat : (Q.map h.op).hom ((η.app V).hom p) = (η.app (op U)).hom ((P.map h.op).hom p) :=
        (congrArg (fun φ => φ.hom p) (η.naturality h.op)).symm
      simp only [NatTrans.comp_app, toSky_app, Limits.comp_zero]
      change (Submodule.mkQ _) ((Q.map h.op).hom (η.app V |>.hom p)) = 0
      rw [nat, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨_, rfl⟩)
    have e2 := congrFun (congrArg (fun φ => (φ.app (op U)).hom y) e) (𝟙 U)
    simp only [toSky_app] at e2
    change (Submodule.mkQ _) ((Q.map (𝟙 U).op).hom y) = 0 at e2
    rw [op_id, Q.map_id, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at e2
    obtain ⟨x, hx⟩ := e2
    exact ⟨x, hx⟩

theorem SecPre_of (hSec : SHSection) : LateralTheory.E.SHEqvPf.SecPre := by
  intro _ q i A hA
  exact toSheafify_bij (R := ZMod q) (Spec A) (fun h S hS => mem_of_cov hSec A hA h S hS) (Scheme.Γ ⋙ twF q i)

end LateralTheory.E.SecPrePf
