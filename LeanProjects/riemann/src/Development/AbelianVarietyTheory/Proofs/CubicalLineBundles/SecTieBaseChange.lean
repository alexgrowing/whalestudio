import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LiftBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ScaledBaseChangeFibreSectionCalculus

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.TieCalc

theorem isoMaps_iff {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
    (σ : LB.Sec L') (s : LB.Sec (L.pull F)) :
    IsoMaps w σ s ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι) (k : L'.ι), F (r z) ∈ L.U j → r z ∈ L'.U k →
      gs r z _ (s.f (fun _ => j)) = (gw w r z j k).val * gs r z _ (σ.f k) := by
  constructor
  · intro h Z r z j k hj hk
    have hz : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
    have a := congrArg (gs r z _) (h (fun _ => j) k)
    exact (gs_res _ z _ hz _).symm.trans (a.trans ((gs_mul _ z _ hz _ _).trans
        (congrArg₂ (· * ·) (gs_unit _ z _ hz _) (gs_res _ z _ hz _))))
  · intro h (i : PUnit → L.ι) k
    exact fn_ext fun p hp =>
      (gs_res _ p _ hp _).trans ((h _ (𝟙 _) p (i PUnit.unit) k (mem_pull.1 hp.1) hp.2).trans
        (Eq.symm ((gs_mul _ p _ hp _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 _) p _ hp _) (gs_res _ p _ hp _)))))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {t : SAB H (Sp S)} (m : SABMap t Xo.univ.t x)

theorem exists_canon : ∃ g : t.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) Xo.univ.t.G).left = m.φ ∧
    g ≫ (fst (Over.mk x) Xo.univ.t.G).left = t.G.hom := by
  let a₀ : Over.mk (t.G.hom ≫ x) ⟶ Over.mk x := Over.homMk t.G.hom rfl
  let b₀ : Over.mk (t.G.hom ≫ x) ⟶ Xo.univ.t.G := Over.homMk m.φ m.cart.1.w
  exact ⟨(lift a₀ b₀).left, congrArg (fun q => q.left) (lift_snd a₀ b₀), congrArg (fun q => q.left) (lift_fst a₀ b₀)⟩

theorem canon_mem {g : t.G.left ⟶ Gx x} (hg : g ≫ (snd (Over.mk x) Xo.univ.t.G).left = m.φ)
    (j : Xo.univ.t.PP.L.ι) (y : t.G.left) (hy : m.φ y ∈ Xo.univ.t.PP.L.U j) : g y ∈ (PPx x).U (fun _ => j) :=
  Set.mem_iInter.2 fun _ => (congrArg (fun q => q y ∈ Xo.univ.t.PP.L.U j) hg).mpr hy

theorem rigIso_unique {w w' : LB.Iso t.PP.L (Xo.univ.t.PP.L.pull m.φ)} (h : RigIso m w) (h' : RigIso m w') :
    w = w' := by
  have hp : IsProper t.G.hom := MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 Xo.univ.proper
  have hab : IsAbelianScheme t.G := ⟨t.semi.comm, t.semi.smooth, hp, t.semi.geomConnected⟩
  exact GlobalTheory.iso_eq_of_maps_along_section (S := Sp S) (exists_chart t.PP.isLB)
    (fun y => (exists_chart Xo.univ.t.PP.isLB (m.φ y)).elim fun j hj => ⟨fun _ => j, mem_pull.2 hj⟩)
    t.G.hom (eSec t.G) (Over.w η[t.G]) (GlobalTheory.globalFns_holds _ _ hab).2 h.1 h'.1 h.2 h'.2

theorem secTie_iff {w : LB.Iso t.PP.L (Xo.univ.t.PP.L.pull m.φ)} (hw : RigIso m w) {g : t.G.left ⟶ Gx x}
    (hs : g ≫ (snd (Over.mk x) Xo.univ.t.G).left = m.φ) (hf : g ≫ (fst (Over.mk x) Xo.univ.t.G).left = t.G.hom)
    (th : LB.Sec t.PP.L) (s : LB.Sec (PPx x)) :
    SecTie m th s ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ t.G.left) (z : Z) (j : Xo.univ.t.PP.L.ι) (k : t.PP.L.ι),
      m.φ (r z) ∈ Xo.univ.t.PP.L.U j → r z ∈ t.PP.L.U k →
      gs (r ≫ g) z ((PPx x).U (fun _ => j)) (s.f (fun _ => j)) = (gw w r z j k).val * gs r z _ (th.f k) := by
  constructor
  · rintro ⟨w', s1, r1, i1, c⟩ Z r z j k hj hk
    obtain rfl : w' = w := rigIso_unique m r1 hw
    have le : (Xo.univ.t.PP.L.pull m.φ).U (fun _ => j) ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j) :=
      fun q hq => canon_mem m hs j q (mem_pull.1 hq)
    refine Eq.trans ?_ ((isoMaps_iff w' th s1).1 i1 Z r z j k hj hk)
    rw [c g hs hf (fun _ => j) le]
    exact (gs_appLE g _ _ le r z (mem_pull.2 hj) _).symm
  · intro a
    obtain ⟨s1, hs1⟩ := thf_secUp ((isGen_iff w).1 hw.1) Xo.univ.t.PP.isLB t.PP.isLB th
    refine ⟨w, s1, hw, (isoMaps_iff w th s1).2 fun Z r z j k hj hk => hs1 Z r z (fun _ => j) k (mem_pull.2 hj) hk, ?_⟩
    intro g' e₁ e₂ (J : PUnit → Xo.univ.t.PP.L.ι) hJ
    obtain rfl : g' = g := SecCalc.pm_ext _ _ (e₁.trans hs.symm) (e₂.trans hf.symm)
    refine fn_ext fun p hp => ?_
    obtain ⟨k, hk⟩ := exists_chart t.PP.isLB p
    rw [hs1 _ (𝟙 _) p J k hp hk, gs_appLE _ _ _ hJ (𝟙 _) p hp, a _ (𝟙 _) p _ k (mem_pull.1 hp) hk]

theorem secTie_scale {th th' : LB.Sec t.PP.L} {s s' : LB.Sec (PPx x)} (h : SecTie m th s) (a : S)
    (hs' : ∀ i, s'.f i = scal x a i * s.f i) :
    SecTie m th' s' ↔ ∀ i, th'.f i = constFn t.G.hom _ a * th.f i := by
  obtain ⟨g, hs, hf⟩ := exists_canon m
  obtain ⟨w, -, hw, -⟩ := id h
  rw [secTie_iff m hw hs hf] at h ⊢
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ t.G.left) (z : Z) (j : Xo.univ.t.PP.L.ι) (k : t.PP.L.ι),
      m.φ (r z) ∈ Xo.univ.t.PP.L.U j → r z ∈ t.PP.L.U k →
      gs (r ≫ g) z ((PPx x).U (fun _ => j)) (s'.f (fun _ => j)) =
        (gw w r z j k).val * gs r z _ (constFn t.G.hom _ a * th.f k) := by
    intro Z r z j k hj hk
    have a₁ : (r ≫ g) z ∈ (PPx x).U (fun _ => j) := canon_mem m hs j _ hj
    rw [gs_mul _ z _ hk, gs_constFn _ _ _ z hk, mul_left_comm]
    refine (congrArg (gs _ z _) (hs' _)).trans ((gs_mul _ z _ a₁ _ _).trans (congrArg₂ (· * ·) ?_ (h Z r z j k hj hk)))
    exact (gs_constFn (fst (Over.mk x) Xo.univ.t.G).left _ _ z a₁ a).trans (by rw [Category.assoc, hf])
  constructor
  · intro h' k
    refine fn_ext fun y hy => ?_
    obtain ⟨j, hj⟩ := exists_chart Xo.univ.t.PP.isLB (m.φ y)
    exact (Units.mul_right_inj _).1 ((h' _ (𝟙 _) y j k hj hy).symm.trans (key _ (𝟙 _) y j k hj hy))
  · intro h' Z r z j k hj hk
    rw [h' k]
    exact key Z r z j k hj hk

theorem secTie_baseChange {th : LB.Sec t.PP.L} {s : LB.Sec (PPx x)} (h : SecTie m th s) {S' : Type} [CommRing S']
    (φ : S →+* S') {x' : Sp S' ⟶ Xo.X} {t'' : SAB H (Sp S')} (m' : SABMap t'' Xo.univ.t x')
    (n : SABMap t'' t (spMap φ)) (s' : LB.Sec (PPx x')) (w : LB.Iso t''.PP.L (t.PP.L.pull n.φ))
    (θ : LB.Sec (t.PP.L.pull n.φ)) (th' : LB.Sec t''.PP.L) (hx : x' = spMap φ ≫ x) (hφ : m'.φ = n.φ ≫ m.φ)
    (hb : SecBC φ 1 x x' s s') (hw : RigIso n w) (hθ : PullSec n.φ th θ) :
    SecTie m' th' s' ↔ IsoMaps w th' θ := by
  obtain ⟨g, hs, hf⟩ := exists_canon m
  obtain ⟨g', hs', hf'⟩ := exists_canon m'
  obtain ⟨w₁, -, hw₁, -⟩ := id h
  obtain ⟨w₂, hw₂, T⟩ := GlobalTheory.LiftBaseChange.rigIso_comp m n m' hx hφ hw₁ hw
  obtain ⟨pm, ps, pf, hp⟩ := hb
  have eg : g' ≫ pm = n.φ ≫ g := by
    apply SecCalc.pm_ext
    · rw [Category.assoc, ps, hs', Category.assoc, hs, hφ]
    · rw [Category.assoc, pf, ← Category.assoc, hf', Category.assoc, hf]
      exact n.cart.1.w.symm
  have ept : ∀ y, m'.φ y = m.φ (n.φ y) := fun y => by rw [hφ]; rfl
  rw [secTie_iff m hw₁ hs hf] at h
  rw [secTie_iff m' hw₂ hs' hf', isoMaps_iff]
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ t''.G.left) (z : Z) (j : Xo.univ.t.PP.L.ι) (i : t.PP.L.ι),
      m.φ (n.φ (r z)) ∈ Xo.univ.t.PP.L.U j → n.φ (r z) ∈ t.PP.L.U i →
      gs (r ≫ g') z ((PPx x').U (fun _ => j)) (s'.f (fun _ => j)) =
        (gw w₁ (r ≫ n.φ) z j i).val * gs r z _ (θ.f (fun _ => i)) := by
    intro Z r z j i hj hi
    have a₁ : (r ≫ g') z ∈ (PPx x').U (fun _ => j) := canon_mem m' hs' j _ (by rw [ept]; exact hj)
    have le : (t.PP.L.pull n.φ).U (fun _ => i) ≤ n.φ ⁻¹ᵁ t.PP.L.U i := fun q hq => mem_pull.1 hq
    have e₁ := hp (fun _ => j) (SecCalc.ppx_le pm ps _)
    rw [SecCalc.scal_one' x (fun _ => j), _root_.one_mul] at e₁
    rw [hθ (fun _ => i) le, gs_appLE n.φ _ _ le r z (mem_pull.2 hi), ← h Z (r ≫ n.φ) z j i hj hi, ← e₁,
      gs_appLE pm _ _ _ (r ≫ g') z a₁, Category.assoc, Category.assoc, eg]
  constructor
  · intro h' Z r z i k hi hk
    obtain ⟨j, hj⟩ := exists_chart Xo.univ.t.PP.isLB (m.φ (n.φ (r z)))
    have e := (key Z r z j i hj hi).symm.trans (h' Z r z j k (by rw [ept]; exact hj) hk)
    rw [T Z r z j i k hj hi hk, Units.val_mul, _root_.mul_assoc] at e
    exact (Units.mul_right_inj _).1 e
  · intro h' Z r z j k hj hk
    obtain ⟨i, hi⟩ := exists_chart t.PP.isLB (n.φ (r z))
    rw [ept] at hj
    rw [key Z r z j i hj hi, h' Z r z i k hi hk, T Z r z j i k hj hi hk, Units.val_mul, _root_.mul_assoc]

theorem secTie_calc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (t' : SAB H (Sp S)) (m : SABMap t' Xo.univ.t x) (th : LB.Sec t'.PP.L) (s : LB.Sec (PPx x)), SecTie m th s → (∀ (a : S) (x' : Sp S ⟶ Xo.X) (s' : LB.Sec (PPx x')) (th' : LB.Sec t'.PP.L), x' = x → SecBC (RingHom.id S) a x x' s s' → (SecTie m th' s' ↔ ∀ i, th'.f i = constFn t'.G.hom _ a * th.f i)) ∧ ∀ (S' : Type) [CommRing S'] (φ : S →+* S') (x' : Sp S' ⟶ Xo.X) (t'' : SAB H (Sp S')) (m' : SABMap t'' Xo.univ.t x') (n : SABMap t'' t' (spMap φ)) (s' : LB.Sec (PPx x')) (w : LB.Iso t''.PP.L (t'.PP.L.pull n.φ)) (θ : LB.Sec (t'.PP.L.pull n.φ)) (th' : LB.Sec t''.PP.L), x' = spMap φ ≫ x → m'.φ = n.φ ≫ m.φ → SecBC φ 1 x x' s s' → RigIso n w → PullSec n.φ th θ → (SecTie m' th' s' ↔ IsoMaps w th' θ) := by
  intro E _ _ _ H Dw l Xo S _ x t' m th s h
  refine ⟨fun a x' s' th' hx hb => ?_, fun S' _ φ x' t'' m' n s' w θ th' hx hφ hb hw hθ =>
    secTie_baseChange m h φ m' n s' w θ th' hx hφ hb hw hθ⟩
  subst hx
  have e : x' = spMap (RingHom.id S) ≫ x' := by rw [SecCalc.spMap_id', Category.id_comp]
  exact secTie_scale m h a
    (((SecCalc.sec_calc E H Dw l Xo S S S (RingHom.id S) (RingHom.id S) x' x' x' e e).2.1 a s s').1 hb)

end GlobalTheory.LamT.TieCalc
