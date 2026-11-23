import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointBaseChangeLaws
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsUUOver
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmonicValuesInvariantUniversalEndomorphismStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShortValMove

open GlobalTheory.TranslMove GlobalTheory.VVRank

section Sections

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A] {φ : A.left ⟶ G.left}
  {T : Over S'} {T₀ : Over S} {L₀ : LB G.left} {L₁ : LB A.left}
  {w : LB.Iso L₁ (L₀.pull φ)} {Ψ : (T ⊗ A).left ⟶ (T₀ ⊗ G).left}

theorem secRel_of_charts (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (h₂ : Ψ ≫ (snd T₀ G).left = (snd T A).left ≫ φ)
    (s₀ : LB.Sec (LPow G L₀ 1 T₀)) (s : LB.Sec (LPow A L₁ 1 T))
    (H : ∀ (i : L₀.ι) (j : L₁.ι) (W : (T ⊗ A).left.Opens),
      W = (snd T A).left ⁻¹ᵁ ((LB.div (L₀.pull φ) L₁).U ((fun _ => i), j)) →
      ∀ (h₀ : W ≤ (snd T A).left ⁻¹ᵁ ((LB.div (L₀.pull φ) L₁).U ((fun _ => i), j)))
      (h₁ : W ≤ Ψ ⁻¹ᵁ (LPow G L₀ 1 T₀).U (fun _ => i)) (h₂ : W ≤ (LPow A L₁ 1 T).U (fun _ => j)),
      (Ψ.appLE ((LPow G L₀ 1 T₀).U (fun _ => i)) W h₁).hom (s₀.f (fun _ => i)) =
        ((snd T A).left.appLE ((LB.div (L₀.pull φ) L₁).U ((fun _ => i), j)) W h₀).hom
          (Units.val (w.s ((fun _ => i), j))) *
        ((T ⊗ A).left.presheaf.map (homOfLE h₂).op).hom (s.f (fun _ => j))) : SecRel w Ψ s₀ s := by
  refine (secRel_iff hL₀ hL₁ h₂ 1 Nat.cast_one.symm s₀ s).2 fun i j W k₀ k₁ k₂ => fn_ext fun x hx => ?_
  have m₁ : (snd T A).left ⁻¹ᵁ ((LB.div (L₀.pull φ) L₁).U ((fun _ => i), j)) ≤
      Ψ ⁻¹ᵁ (LPow G L₀ 1 T₀).U (fun _ => i) := fun p hp => Set.mem_iInter.2 fun _ => by
    have h : ((snd T A).left ≫ φ) p ∈ L₀.U i := mem_pull.1 hp.1
    rw [← h₂] at h
    exact h
  have m₂ : (snd T A).left ⁻¹ᵁ ((LB.div (L₀.pull φ) L₁).U ((fun _ => i), j)) ≤
      (LPow A L₁ 1 T).U (fun _ => j) := fun p hp => Set.mem_iInter.2 fun _ => hp.2
  have e := congrArg (gs (𝟙 _) x _) (H i j _ rfl le_rfl m₁ m₂)
  have hx' : (𝟙 (T ⊗ A).left : _ ⟶ _) x ∈ W := hx
  have hx₀ := k₀ hx'
  rw [gs_mul _ _ _ hx₀, TranslMove.gs_appLE _ _ _ _ _ _ hx₀, TranslMove.gs_appLE _ _ _ _ _ _ hx₀,
    gs_res _ _ _ hx₀] at e
  rw [pow_one, gs_mul _ _ _ hx', TranslMove.gs_appLE _ _ _ _ _ _ hx', TranslMove.gs_appLE _ _ _ _ _ _ hx',
    gs_res _ _ _ hx']
  exact e

end Sections

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem sv_pull {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hs : pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left)
    {s : LB.Sec (PPx x)} {s' : LB.Sec (PPx x')}
    (ha : ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i),
      (pm.appLE _ _ h).hom (s.f i) = s'.f i)
    {Z : Scheme.{0}} (r : Z ⟶ Gx x') (z : Z) {J} (hJ : Good Xo.univ.t.PP.L z J) :
    sv Xo.univ.t.G s (r ≫ pm) z J = sv Xo.univ.t.G s' r z J := by
  have hm := hJ.mem (fun _ : Fin 1 => (snd (Over.mk x') Xo.univ.t.G).left) r
  refine (sval_of s (r ≫ pm) z J (fun _ => J (r ≫ (snd (Over.mk x') Xo.univ.t.G).left))
    (fun _ => by rw [Category.assoc, hs])).trans ?_
  refine (TranslMove.gs_appLE r pm z _ _ (FramedBaseChange.chart_le pm hs _) hm _).symm.trans ?_
  exact congrArg (gs r z _) (ha _ _)

theorem exists_ptEquiv {S : Type} [CommRing S] {ρ : Xo.X ⟶ Xo.X} (ν : SABMap Xo.univ.t Xo.univ.t ρ)
    {x x' : Sp S ⟶ Xo.X} (hx : x' = x ≫ ρ) :
    ∃ e : (ptO Xo x ⟶ Xo.univ.t.G) ≃* (ptO Xo x' ⟶ Xo.univ.t.G), ∀ p, (e p).left = p.left ≫ ν.φ := by
  subst hx
  refine ⟨MulEquiv.ofBijective (pushHom ν.cart (ptO Xo x)) ⟨fun p q h => ?_, fun q => ?_⟩, fun p => rfl⟩
  · exact Over.OverMorphism.ext (ν.cart.1.hom_ext (congrArg (fun t => t.left) h)
      ((Over.w p).trans (Over.w q).symm))
  · exact ⟨Over.homMk (ν.cart.1.lift q.left x (Over.w q)) (ν.cart.1.lift_snd _ _ _),
      Over.OverMorphism.ext (ν.cart.1.lift_fst _ _ _)⟩

theorem exists_move_baseChange {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    {ρ : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ} {y y' : FrPt Xo c S} (hm : FrMove ρ ν y y')
    {φ : S →ₐ[c.F] T} {z z' : FrPt Xo c T} (h : FrMap φ y z) (h' : FrMap φ y' z') :
    z'.x = z.x ≫ ρ ∧ (∀ τ i, z'.u τ i = z.u τ i ≫ ν.φ) ∧
    ∃ (pm : Gx z.x ⟶ Gx z'.x) (w : LB.Iso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull ν.cm.F)),
      pm ≫ (fst (Over.mk z'.x) Xo.univ.t.G).left = (fst (Over.mk z.x) Xo.univ.t.G).left ∧
      pm ≫ (snd (Over.mk z'.x) Xo.univ.t.G).left = (snd (Over.mk z.x) Xo.univ.t.G).left ≫ ν.φ ∧
      CubIso ν w ∧ SecRel (T := Over.mk z.x) (T₀ := Over.mk z'.x) w pm z'.s z.s := by
  obtain ⟨hx, hu, pm, w, hf, hs, hw, hc⟩ := hm
  obtain ⟨gx, gu, p, ps, pf, pa⟩ := h
  obtain ⟨gx', gu', p', ps', pf', pa'⟩ := h'
  have hL := Xo.univ.t.PP.isLB
  have ex : z'.x = z.x ≫ ρ := by rw [gx', gx, hx, Category.assoc]
  have sq : (fst (Over.mk z.x) Xo.univ.t.G).left ≫ z'.x =
      ((snd (Over.mk z.x) Xo.univ.t.G).left ≫ ν.φ) ≫ Xo.univ.t.G.hom := by
    rw [Category.assoc, ν.cart.1.w, ex, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ ρ) ((Over.w (fst (Over.mk z.x) Xo.univ.t.G)).trans
      (Over.w (snd (Over.mk z.x) Xo.univ.t.G)).symm)
  let q : Gx z.x ⟶ Gx z'.x := pullback.lift (f := z'.x) (g := Xo.univ.t.G.hom) _ _ sq
  have qf : q ≫ (fst (Over.mk z'.x) Xo.univ.t.G).left = (fst (Over.mk z.x) Xo.univ.t.G).left :=
    pullback.lift_fst _ _ _
  have qs : q ≫ (snd (Over.mk z'.x) Xo.univ.t.G).left = (snd (Over.mk z.x) Xo.univ.t.G).left ≫ ν.φ :=
    pullback.lift_snd _ _ _
  have comm : q ≫ p' = p ≫ pm := FramedBaseChange.pulledGroup_hom_ext _ _
    (by rw [Category.assoc, ps', qs, Category.assoc, hs, ← Category.assoc, ps])
    (by rw [Category.assoc, pf', ← Category.assoc, qf, Category.assoc, hf, pf])
  have R := secRel_of_charts (T := Over.mk y.x) (T₀ := Over.mk y'.x) hL hL hs y'.s y.s hc
  refine ⟨ex, fun τ i => by rw [gu', gu, hu, Category.assoc], q, w, qf, qs, hw, fun Z r t J₀ J hJ₀ hJ => ?_⟩
  have a₁ := sv_pull p' ps' pa' (r ≫ q) t hJ₀
  have a₂ := sv_pull p ps pa r t hJ
  have a₃ := R Z (r ≫ p) t J₀ J hJ₀ hJ
  rw [Category.assoc, comm, ← Category.assoc] at a₁
  rw [Category.assoc r p (snd (Over.mk y.x) Xo.univ.t.G).left, ps] at a₃
  exact a₁.symm.trans (a₃.trans (congrArg _ a₂))

theorem eta_congr {a b : Dw.La}
    (h : (Submodule.Quotient.mk a : LevQ Dw l) = Submodule.Quotient.mk b) : Xo.univ.eta a = Xo.univ.eta b := by
  have h2 := Xo.univ.eta_add (a - b) b
  rwa [sub_add_cancel, Xo.univ.eta_ker _ ((Submodule.Quotient.eq _).1 h), _root_.one_mul] at h2

theorem mk_levRep (q : LevQ Dw l) : (Submodule.Quotient.mk (levRep q) : LevQ Dw l) = q :=
  Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)

theorem shortValAt_move : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S : Type) [CommRing S] [Algebra c.F S] (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (gM gA : Dw.La →ₗ[𝓞 E] Dw.La) (y y' : FrPt Xo c S), IsLevMove ρ ν gM gA → FrMove ρ ν y y' → ∀ σq : LevQ Dw l ≃ LevQ Dw l, (∀ a, σq (Submodule.Quotient.mk a) = Submodule.Quotient.mk (gM a)) → ∀ (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (β : c.F) (N : ℕ) (v : S), ShortValAt Xo c nab w Λ β N P y' v → ShortValAt Xo c nab (fun q => w (fun b => σq.symm (q b))) Λ β N P y v := by
  intro hLaw hCI E _ _ _ H Dw l Xo c _ nab hnab S _ _ ρ ν gM gA y y' hlev hmv σq hσ n a P hP w Λ β N v hv
  obtain ⟨S', _, _, φ, y₁', z', tp', F', hff, hfr, hZ, hG, htp, hUU, hval⟩ := hv
  obtain ⟨y₁, hy₁⟩ := GlobalTheory.FramedBaseChange.exists_frMap hLaw E H Dw l Xo c S S' φ y
  obtain ⟨hx, hu, pm, ω, hf, hs, hω, hR⟩ := exists_move_baseChange hmv hy₁ hfr
  have hL := Xo.univ.t.PP.isLB
  obtain ⟨e, he⟩ := exists_ptEquiv ν hx
  have he' : ∀ p, p.left = (e.symm p).left ≫ ν.φ := fun p => by rw [← he, e.apply_symm_apply]
  have hact : ∀ p b, e (p ≫ Xo.univ.t.act.act b) = e p ≫ Xo.univ.t.act.act b := fun p b =>
    Over.OverMorphism.ext (by
      rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, Category.assoc, ν.act])
  have hact' : ∀ p b, e.symm p ≫ Xo.univ.t.act.act b = e.symm (p ≫ Xo.univ.t.act.act b) := fun p b =>
    e.injective (by rw [hact, e.apply_symm_apply, e.apply_symm_apply])
  have hlv : ∀ q : LevQ Dw l, e (levPt Xo y₁.x (levRep q)) = levPt Xo y₁'.x (levRep (σq.symm q)) := fun q => by
    have h1 : Xo.univ.eta (levRep q) = Xo.univ.eta (gM (levRep (σq.symm q))) :=
      eta_congr (by rw [← hσ, mk_levRep, mk_levRep, σq.apply_symm_apply])
    refine Over.OverMorphism.ext ?_
    rw [he, levPt, levPt, h1, Over.comp_left, Over.comp_left, Category.assoc, hlev.2.1, Over.toUnit_left,
      Over.toUnit_left]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hx.symm)
  choose F hF hFF using fun (q : Fin n → LevQ Dw l) i b =>
    isUUOver_move hLaw E H Dw l Xo c S' ρ ν y₁ y₁' pm ω hx hf hs hω
      ((secRel_iff hL hL hs 1 Nat.cast_one.symm y₁'.s y₁.s).1 hR) N (e.symm (z' i b))
      (e.symm (tp' (fun b => σq.symm (q b)) b)) (z' i b) (tp' (fun b => σq.symm (q b)) b) (he' _) (he' _)
      (F' (fun b => σq.symm (q b)) i b) (hUU _ i b)
  refine ⟨S', inferInstance, inferInstance, φ, y₁, fun i b => e.symm (z' i b),
    fun q b => e.symm (tp' (fun b => σq.symm (q b)) b), F, hff, hy₁, fun i => ⟨fun b => ?_, ?_⟩, ?_,
    fun q b => ⟨?_, ?_⟩, hF, ?_⟩
  · rw [← map_pow, (hZ i).1 b, map_one]
  · intro mu hmu cm hcm k
    have h := congrArg e.symm ((hZ i).2 mu hmu cm hcm k)
    rw [map_list_prod, List.map_ofFn, map_one] at h
    simp only [hact']
    exact h
  · intro k _ ψ g hg i j hij
    refine hG k ψ (Over.homMk (spMap ψ) rfl) rfl (funext fun b => Over.OverMorphism.ext ?_)
    have h := congrArg (fun t => t.left ≫ ν.φ) (congrFun hij b)
    simp only [Over.comp_left, hg, Category.assoc, ← he'] at h
    exact h
  · rw [← map_pow, (htp _ b).1, ← hlv, e.symm_apply_apply]
  · obtain ⟨j, hj⟩ := (htp (fun b => σq.symm (q b)) b).2
    exact ⟨j, fun t ht => by rw [hact', hj t ht, map_one]⟩
  · rw [hval]
    congr 1
    refine (finsum_comp_equiv (Equiv.piCongrRight fun _ : Fin n => σq.symm)).symm.trans
      (finsum_congr fun q => ?_)
    refine congrArg₂ (· * ·) rfl (Finset.sum_congr rfl fun i _ => ?_)
    exact GlobalTheory.T.harmonic_values_invariant_universal_endomorphism hLaw hCI E H Dw l Xo c nab hnab S' ρ ν y₁ y₁' pm ω hx hf hs hω hu n a P hP N
      (F q i) (F' (fun b => σq.symm (q b)) i) (hFF q i)

end GlobalTheory.ShortValMove
