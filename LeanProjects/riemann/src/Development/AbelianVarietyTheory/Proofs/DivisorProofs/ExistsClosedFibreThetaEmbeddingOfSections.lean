import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendFiniteModif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTailFurther
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupNonzeroLocusEmbH
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitRedCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemEmbHOfClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToProjSecPullSecPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedFibrePt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.SecEmb.geometricallyIrreducible_of_smooth {X S : Scheme.{0}} (f : X ⟶ S) (hs : Smooth f)
    (hc : GeometricallyConnected f) : GeometricallyIrreducible f := by
  constructor
  intro K _ g Z fst snd h
  have : Smooth snd := MorphismProperty.of_isPullback (P := @Smooth) h hs
  have hcs := hc.geometrically_connectedSpace g fst snd h
  exact GlobalTheory.irreducibleSpace_of_smooth_field_of_connectedSpace K Z snd this hcs

theorem GlobalTheory.Mum.SecEmb.emb_of_traitRed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (M : Modif R) (G : Over M.S) [GrpObj G],
    IsSemiAbelian G → ∀ (B L : LB G.left), B.IsLB → L.IsLB → ∀ (N : ℕ) (s : Fin (N + 1) → B.Sec) (θ : L.Sec)
    (Y : Over (Sp (ResidueField R))) [GrpObj Y], Smooth Y.hom → ∀ (j : Y.left ⟶ PSpace R N),
    j ≫ PSpace.str R N = Y.hom ≫ spMap (residue R) → IsImmersion j → ∀ (O : Y.left.Opens), (O : Set Y.left).Nonempty →
    GlobalTheory.Mum.SecEmb.TraitRed M G s θ Y j O → ∃ E : Emb M.π G, E.Theta L := by
  intro R _ _ _ hR M G _ hG B L hB hL N s θ Y _ hY j hj hi O hO hT
  have hH := GlobalTheory.Mum.SecEmb.mem_embH_of_closed R hR M G hG B L hB hL N s θ Y hY j hj hi O hT
  exact ⟨{ N := N
           H := GlobalTheory.Mum.SecEmb.embH s
           H_all := hH
           f := GlobalTheory.Mum.SecEmb.embF (G.hom ≫ M.π) s
           f_over := GlobalTheory.ProjSpace.toProj_str _ _ _
           Y := Y
           smooth := hY
           j := j
           j_over := hj
           imm := hi
           fib := fun Ω _ x κ hx => GlobalTheory.Mum.SecEmb.Fib.fib R hR M G hG B L hB hL N s θ Y hY j hj hi O hT hH Ω x κ hx },
    θ, O, hO, fun g y hy hc hf => GlobalTheory.Mum.SecEmb.ThetaPt.mem_basicOpen_theta R hR M G hG B L hB hL N s θ Y hY j hj hi O hT g y hy hc hf⟩

namespace GlobalTheory.Mum.SecEmb

theorem agree_pull {X P Q : Scheme.{0}} (L : LB X) {hP : P ⟶ X} {hQ : Q ⟶ X} (g : Q ⟶ P) (e : g ≫ hP = hQ) {k : ℕ}
    (σ : SecK L hP k) : ∃ σ' : SecK L hQ k, ∀ {Y : Scheme.{0}} {h : Y ⟶ X} (s : SecK L h k), Agree L σ s → Agree L σ' s := by
  subst e
  refine ⟨ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec σ g, fun s hs Z p p' hp z J hJ => ?_⟩
  rw [ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec σ g p z hJ]
  exact hs Z (p ≫ g) p' (by rw [Category.assoc]; exact hp) z J hJ

theorem traitReg_of_secs {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G : Over M.S) [GrpObj G]
    (L : LB G.left) {A : Scheme.{0}} (α : A ⟶ G.left) (Sc : Secs M G L α) :
    (∀ i, TraitReg M G L (Sc.s i)) ∧ TraitReg M G L Sc.θ := by
  constructor
  · intro i W _ _ _ hW φ ξ hinj hloc hξ
    obtain ⟨W', i1, i2, i3, io, G', iG', β, σ, θ', κ, e, hW', hio, hfin, hpb, -, -, hσ, -, -⟩ :=
      Sc.trait W hW φ ξ hinj hloc hξ
    obtain ⟨σ'', h''⟩ := agree_pull L hpb.1.isoPullback.inv hpb.1.isoPullback_inv_fst (σ i)
    exact ⟨W', i1, i2, i3, io, σ'', hW', hio, hfin, h'' _ (hσ i)⟩
  · intro W _ _ _ hW φ ξ hinj hloc hξ
    obtain ⟨W', i1, i2, i3, io, G', iG', β, σ, θ', κ, e, hW', hio, hfin, hpb, -, -, -, hθ, -⟩ :=
      Sc.trait W hW φ ξ hinj hloc hξ
    obtain ⟨σ'', h''⟩ := agree_pull L hpb.1.isoPullback.inv hpb.1.isoPullback_inv_fst θ'
    exact ⟨W', i1, i2, i3, io, σ'', hW', hio, hfin, h'' _ hθ⟩

theorem core : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (C C' : LabCover D) (Sc : Secs C.toModif C.G C.P.L.L C.α) (h : C'.S ⟶ C.S) (β : C'.G.left ⟶ C.G.left),
    h ≫ C.π = C'.π → IsGrpPullback C'.G C.G h β → LBIso C'.P.L.L (C.P.L.L.pull β) →
    (∀ i, ∃ σ : SecK C.P.L.L β Sc.k, Agree C.P.L.L σ (Sc.s i)) → (∃ θ : SecK C.P.L.L β 1, Agree C.P.L.L θ Sc.θ) →
    ∃ E : Emb C'.π C'.G, E.Theta C'.P.L.L := by
  intro R _ _ _ hR D C C' Sc h β hπ hpb hL hs hθ
  choose σ hσ using hs
  obtain ⟨θ₀, hθ₀⟩ := hθ
  obtain ⟨θ, hT⟩ := GlobalTheory.Mum.SecEmb.traitRed_cover R hR D C C' Sc h β hπ hpb hL σ hσ θ₀ hθ₀
  exact GlobalTheory.Mum.SecEmb.emb_of_traitRed R hR C'.toModif C'.G C'.semi _ C'.P.L.L (LB.isLB_linComb C.P.L.isLB _ _) C'.P.L.isLB Sc.N σ θ Sc.Y Sc.smooth
    Sc.j Sc.j_over Sc.imm Sc.O Sc.O_ne hT

theorem emb_of_secs : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (C : LabCover D), Nonempty (Secs C.toModif C.G C.P.L.L C.α) → ∃ (C' : LabCover D) (E : Emb C'.π C'.G), E.Theta C'.P.L.L := by
  intro R _ _ _ hR D C ⟨Sc⟩
  have hR' := hR
  obtain ⟨⟨hN, -, -, -⟩, hc⟩ := hR'
  have hsemi := C.semi
  obtain ⟨hs, hθ⟩ := traitReg_of_secs C.toModif C.G C.P.L.L C.α Sc
  obtain ⟨M', h, -, hgp, hπ, hσ⟩ := GlobalTheory.Mum.extend_finiteModif R C.toModif C.G hsemi.smooth hsemi.quasiCompact
    (GlobalTheory.Mum.SecEmb.geometricallyIrreducible_of_smooth _ hsemi.smooth hsemi.geomConnected) C.P.L.L C.P.L.isLB C.A.A.left C.α C.A.A.hom C.α_cart.1
    (Option (Fin (Sc.N + 1))) (fun o => o.elim 1 (fun _ => Sc.k))
    (Option.rec (motive := fun o => SecK C.P.L.L C.α (o.elim 1 (fun _ => Sc.k))) Sc.θ Sc.s)
    (by rintro (_ | i); exacts [hθ, hs i])
  obtain ⟨C', eS, β, hπ', hpb, hL⟩ := GlobalTheory.Mum.LabCover.exists_pull R D C M' h hgp hπ
  have hw : β ≫ C.G.hom = (C'.G.hom ≫ eS.hom) ≫ h := by rw [Category.assoc]; exact hpb.1.w
  refine ⟨C', core R hR D C C' Sc (eS.hom ≫ h) β (by rw [Category.assoc, hπ, hπ']) hpb hL ?_ ?_⟩
  · intro i
    obtain ⟨σ, hσi⟩ := hσ (some i)
    obtain ⟨σ', h'⟩ := agree_pull C.P.L.L (pullback.lift β (C'.G.hom ≫ eS.hom) hw) (pullback.lift_fst _ _ _) σ
    exact ⟨σ', h' _ hσi⟩
  · obtain ⟨σ, hσi⟩ := hσ none
    obtain ⟨σ', h'⟩ := agree_pull C.P.L.L (pullback.lift β (C'.G.hom ≫ eS.hom) hw) (pullback.lift_fst _ _ _) σ
    exact ⟨σ', h' _ hσi⟩

end GlobalTheory.Mum.SecEmb
