import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapePrimitivityPullbackDescent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsKsMatrixStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelAbelianSchemeConstOverDualNumbers
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardTypeLe
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAdaptedLieBasis

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PelTangent

open GlobalTheory.ShapePull

def chartPullSection {X Y : Scheme.{0}} (L : LB X) (F : Y ⟶ X) (r : X ⟶ Y) (e : r ≫ F = 𝟙 X) :
    ChartPull L (L.pull F) r :=
  have m : ∀ i y, y ∈ L.U i → r y ∈ (L.pull F).U (fun _ => i) := fun i y hy => mem_pull.2 (by
    have : F (r y) = y := congrArg (fun g : X ⟶ X => g y) e
    rw [this]; exact hy)
  { idx := fun i _ => i
    le := fun i y hy => m i y hy
    g := fun y i j hi hj =>
      ((gm_pull_g L F r y (fun _ => i) (fun _ => j) (m i y hi) (m j y hj)).trans (by rw [e])).symm }

section Group

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem exists_oAct (h : IsGrpPullback G' G f φ) {O : Type} [CommRing O] (a : OAct O G) :
    ∃ a' : OAct O G', ∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act c).left := by
  choose w hw pa using fun c => (haveI := a.hom c; GlobalTheory.SymBaseChange.exists_endo h (a.act c))
  have hl : ∀ c, (w c).left ≫ φ = φ ≫ (a.act c).left := fun c => by
    have := congrArg (fun z => z.left) (pa c (𝟙 G'))
    simpa [pushPt] using this
  refine ⟨⟨w, hw, ?_, fun c d => ?_, fun c d => ?_⟩, hl⟩
  · exact eq_up h _ (push_end h (hl 1)) (push_id h) a.one
  · exact eq_up h _ (push_end h (hl _)) (push_comp h _ (push_end h (hl c)) (hl d)) (a.mul c d)
  · exact eq_up h _ (push_end h (hl _)) (push_mul h _ (push_end h (hl c)) (push_end h (hl d))) (a.add c d)

theorem adj_up [IsCommMonObj G] [IsCommMonObj G'] (h : IsGrpPullback G' G f φ) {L : LB G.left} {L' : LB G'.left}
    (hL : L.IsLB) (hL' : L'.IsLB) (H : LBIso L' (L.pull φ)) {w v : G ⟶ G} {w' v' : G' ⟶ G'}
    (hw : w'.left ≫ φ = φ ≫ w.left) (hv : v'.left ≫ φ = φ ≫ v.left)
    (A : LBIso (cubeLB G ![fst G G ≫ w, snd G G] L) (cubeLB G ![fst G G, snd G G ≫ v] L)) :
    LBIso (cubeLB G' ![fst G' G' ≫ w', snd G' G'] L') (cubeLB G' ![fst G' G', snd G' G' ≫ v'] L') :=
  iso_up (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL' _ _)
    (DVR.linComb_isLB _ hL' _ _) (iso_cubeLB_pull h _ H (push_comp h _ (push_fst h) hw) (push_snd h))
    (iso_cubeLB_pull h _ H (push_fst h) (push_comp h _ (push_snd h) hv)) A

theorem prim_up [IsCommMonObj G] [IsCommMonObj G'] (h : IsGrpPullback G' G f φ) {L : LB G.left} {L' : LB G'.left}
    (hL : L.IsLB) (hL' : L'.IsLB) (H : LBIso L' (L.pull φ)) {w : G ⟶ G} {w' : G' ⟶ G'}
    (hw : w'.left ≫ φ = φ ≫ w.left) (A : LBIso L (cubeLB G ![𝟙 G, w] L)) :
    LBIso L' (cubeLB G' ![𝟙 G', w'] L') := by
  have i : LBIso (cubeLB G' ![𝟙 G', w'] L') ((cubeLB G ![𝟙 G, w] L).pull φ) :=
    iso_cubeLB_pull h (selfMap h) H (push_id h) (push_end h hw)
  have a : (cubeLB G ![𝟙 G, w] L).IsLB := DVR.linComb_isLB _ hL _ _
  have a' : (cubeLB G' ![𝟙 G', w'] L').IsLB := DVR.linComb_isLB _ hL' _ _
  exact iso_up hL a hL' a' H i A

end Group

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cmHostUnit_add_conj_eq_one (H : Host E) : H.w0 + H.bar H.w0 = 1 := by
  have h1 : H.bar H.rt ^ 2 = H.rt ^ 2 := by
    rw [← map_pow, H.rt_sq, map_neg, map_natCast]
  have h2 : 2 * H.bar H.w0 = 1 + H.bar H.rt := by
    have := congrArg H.bar H.two_weight_eq_one_add_root
    simpa [map_ofNat] using this
  have h3 : H.bar H.rt = -H.rt := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with e | e
    · exfalso
      have e' : IsCMField.complexConj E (H.rt : E) = H.rt := by rw [← H.bar_eq, e]
      obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
      have c := IsCMField.complexEmbedding_complexConj E φ (H.rt : E)
      rw [e'] at c
      have r : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
        have := congrArg (fun z : 𝓞 E => φ (z : E)) H.rt_sq
        simpa using this
      obtain ⟨x, hx⟩ := Complex.conj_eq_iff_real.1 c.symm
      rw [hx] at r
      have r' : x ^ 2 = -(H.d : ℝ) := by exact_mod_cast r
      have : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
      nlinarith [sq_nonneg x]
    · exact e
  have : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1 := by
    rw [mul_add, h2, H.two_weight_eq_one_add_root, h3]; ring
  exact mul_left_cancel₀ two_ne_zero this

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'')
    (h : R →+* R'') (e : g.comp f = h) : spMap g ≫ spMap f = spMap h := by
  subst e
  exact (Spec.map_comp _ _).symm

theorem tangent_le_dim : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (ρ : o) (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (r : ℕ) (β : o →+* K) (t : TObj g k J b (spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β))) (τ : SAB H (Sp (TrivSqZeroExt K (Fin r → K)))), a w = H.w0 → a w' = H.bar H.w0 → ρ ^ 2 = -(H.d : o) → IsPEL D a bas ρ t τ → (∀ (lam : (Fin r → K) →ₗ[K] K) (t' : TObj g k J b (spMap ((algebraMap K (DualNumber K)).comp β))), TMap t' t (spMap (dirMap lam)) → TMap t' t (constPt (spMap (dirMap lam))) → lam = 0) → r ≤ D.dim := by
  intro L1 L2 L3 E _ _ _ H D g J a w w' bas k o _ b ρ K _ _ _ r β t τ hw hw' hρ ⟨e, he, hL, hact, hdet⟩ hlam
  letI := t.ab.comm
  let p : Sp K ⟶ Sp (TrivSqZeroExt K (Fin r → K)) := spMap (TrivSqZeroExt.fstHom K K (Fin r → K)).toRingHom
  let q : Sp K ⟶ Sp (DualNumber K) := spMap (TrivSqZeroExt.fstHom K K K).toRingHom
  have hp : p ≫ spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) = spMap β :=
    spMap_comp _ _ _ (by ext x; simp [TrivSqZeroExt.algebraMap_eq_inl])
  obtain ⟨t₀, T₀⟩ := GlobalTheory.tObj_pull o g k J b _ _ _ _ p t hp
  obtain ⟨φ₀, h₀, hL₀, hpt₀, hact₀⟩ := id T₀
  letI := t₀.ab.comm

  have : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  have h₁ : IsGrpPullback t.A τ.G (𝟙 _) e.inv.left := isGrpPullback_of_iso e.symm
  have ih : e.inv.left ≫ e.hom.left = 𝟙 _ := by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]
  have hL₁ : LBIso t.L (τ.PP.L.pull e.inv.left) :=
    LBIso.chartPull (chartPullSection t.L _ _ ih) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull τ.PP.L _ _ rfl) hL.symm
  obtain ⟨A, hA⟩ := exists_oAct h₁ τ.act
  obtain ⟨A₀, hA₀⟩ := exists_oAct h₀ A
  have hj : ∀ j, (t.act j).left ≫ e.inv.left = e.inv.left ≫ (τ.act.act (a j)).left := fun j => by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    rw [Iso.comp_inv_eq, Category.assoc, hact, e.inv_hom_id_assoc]
  have adj := fun c => adj_up h₁ τ.PP.isLB t.isLB hL₁ (hA c) (hA (H.bar c)) (τ.adj c)
  have prim : t.Prim w w' := by
    refine ⟨eq_up h₁ _ (push_mul h₁ _ (push_end h₁ (hj w)) (push_end h₁ (hj w'))) (push_id h₁) ?_,
      adj_up h₁ τ.PP.isLB t.isLB hL₁ (hj w) (hj w') ?_, prim_up h₁ τ.PP.isLB t.isLB hL₁ (hj w) ?_⟩
    · rw [hw, hw', ← τ.act.add, cmHostUnit_add_conj_eq_one, τ.act.one]
    · rw [hw, hw']; exact τ.adj _
    · rw [hw]; exact τ.prim
  have det : DetCond D A₀ (𝟙 (Sp K)) (β ρ) := fun σ => by
    have key : ∀ n, LieMult τ.act p σ n → LieMult A₀ (𝟙 (Sp K)) σ n := fun n hn =>
      (GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ A A₀ h₀ hA₀ K _ σ n).2
        ((GlobalTheory.LiePull.lieMult_pull _ _ _ _ _ _ _ τ.act A h₁ hA K _ σ n).2 (by
          rw [Category.comp_id, Category.id_comp]; exact hn))
    have := (hdet K p β hp).1 σ
    exact ⟨fun x => key _ (this.1 x), fun x => key _ (this.2 x)⟩
  obtain ⟨n, v, ty, hv, hty, hdiag⟩ := GlobalTheory.exists_adapted_lieBasis E H D K t₀.A A₀ (β ρ) t₀.ab.smooth det
  obtain ⟨Θ, hsym, hcomm, hker⟩ := GlobalTheory.T.exists_ksMatrix_alt L1 L2 L3 K r t.pol t₀.pol φ₀ n v h₀ hL₀ hv
  have inj : Function.Injective Θ := by
    rw [injective_iff_map_eq_zero]
    intro lam h0
    let d : Sp (DualNumber K) ⟶ Sp (TrivSqZeroExt K (Fin r → K)) := spMap (dirMap lam)
    have hd : d ≫ spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) =
        spMap ((algebraMap K (DualNumber K)).comp β) :=
      spMap_comp _ _ _ (by ext x <;> simp [dirMap, TrivSqZeroExt.algebraMap_eq_inl])
    have hq : q ≫ d = p := spMap_comp _ _ _ (by ext x; simp [dirMap])
    obtain ⟨t', T'⟩ := GlobalTheory.tObj_pull o g k J b _ _ _ _ d t hd
    obtain ⟨ψ, h', hL', hpt', hact'⟩ := id T'
    letI := t'.ab.comm
    obtain ⟨ψ₀, k₀, k₁⟩ := hker lam h0 t'.A ψ h'
    let io : t₀.A.left ⟶ t'.A.left := h'.1.lift φ₀ (t₀.A.hom ≫ q) (by rw [h₀.1.w, Category.assoc, hq])
    have i₁ : io ≫ ψ = φ₀ := h'.1.lift_fst _ _ _
    have i₂ : io ≫ t'.A.hom = t₀.A.hom ≫ q := h'.1.lift_snd _ _ _
    have prim' : t'.Prim w w' :=
      ⟨eq_up h' _ (push_mul h' _ (push_end h' (hact' w)) (push_end h' (hact' w'))) (push_id h') prim.1,
        adj_up h' t.isLB t'.isLB hL' (hact' w) (hact' w') prim.2.1, prim_up h' t.isLB t'.isLB hL' (hact' w) prim.2.2⟩
    have c₁ : IsGrpPullback t₀.A t'.A q io := h'.cancel (h₀.congr hq.symm i₁.symm) i₂
    have c₂ : LBIso t₀.L (t'.L.pull io) :=
      LBIso.trans t₀.isLB (pull_isLB t.isLB φ₀) (pull_isLB t'.isLB io) hL₀
        (LBIso.chartPull (chartPullSame t.L _ _ _ io fun _ => i₁.symm) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull t'.L io io rfl) hL'.symm)
    have c₃ : ∀ i, (t₀.pt i).left ≫ io = q ≫ (t'.pt i).left := fun i => by
      apply h'.1.hom_ext
      · rw [Category.assoc, i₁, hpt₀, Category.assoc, hpt', ← Category.assoc, hq]
      · rw [Category.assoc, i₂, ← Category.assoc, Over.w, Category.assoc, Over.w]
        exact (Category.id_comp _).trans (Category.comp_id _).symm
    have c₄ : ∀ j, (t₀.act j).left ≫ io = io ≫ (t'.act j).left := fun j => by
      apply h'.1.hom_ext
      · rw [Category.assoc, i₁, hact₀, Category.assoc, hact', ← Category.assoc, i₁]
      · rw [Category.assoc, i₂, ← Category.assoc, Over.w, Category.assoc, Over.w, i₂]
    have T₁ := GlobalTheory.ConstTheta.tMap_of_const L1 L2 L3 o g k J b w w' K _ _ t' t₀ io ψ₀ prim' c₁ c₂ c₃ c₄ k₀ (k₁ io i₁ i₂)
    have T₂ := ((GlobalTheory.ZM.tmap_id_comp_cancel o g k J b _ _ _ _ _ _ t t₀ t').2 _ _ T₀).1 T₁
    refine hlam lam t' T' ?_
    show TMap t' t (_ ≫ q ≫ d)
    rw [hq]
    exact T₂
  have hρ' : β ρ ^ 2 = -(H.d : K) := by rw [← map_pow, hρ, map_neg, map_natCast]
  have B := GlobalTheory.SymSignature.finrank_le E H D.p D.q n K (β ρ) ty (LinearMap.range Θ) hρ' hty (by
    rintro _ ⟨lam, rfl⟩
    exact ⟨hsym lam, fun c => hcomm (A.act c) (A.act (H.bar c)) (A₀.act c) (A₀.act (H.bar c)) _ _ (A.hom _) (A.hom _)
      (hA₀ _) (hA₀ _) (adj c) (hdiag c) (hdiag (H.bar c)) lam⟩)
  rw [LinearMap.finrank_range_of_inj inj] at B
  simpa [Datum.dim, Module.finrank_linearMap] using B

end GlobalTheory.PelTangent
