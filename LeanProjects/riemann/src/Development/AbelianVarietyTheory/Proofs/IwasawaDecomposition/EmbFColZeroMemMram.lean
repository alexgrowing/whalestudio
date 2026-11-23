import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HermitianCodeWordWeilElementMemQuadraticField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianLatticeChartFamilyFamOk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightLawGoodOfFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianLatticeChartFamilyLawBasis
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSmulOfDecoEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeMovePreservingLocalParts
import Formalism.LocalToGlobal.Columns.ToHLatLemmas

noncomputable section

namespace GlobalTheory.Mem.Col2.StepZero

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory.HLatOps
open scoped ComplexOrder

section Metric

variable {K : Type} [Field K] [NumberField K] [StarRing K] (C : CSD K)

@[reducible] def valDatum : GSD K where
  G := Unit
  D := Unit
  V := C.V
  ιV := C.ιV
  bV := C.bV
  pair := C.pair
  ρ := 1
  Nab _ := ⊥
  Del _ := ⊥

theorem majAt_eq_classSum (hb : C.HasRatBasis) (hp : ∀ v : InfinitePlace K, (C.H.map v.embedding).PosDef)
    (v : InfinitePlace K) (x y : C.Forms) :
    Formalism.HermitianLatticesTheory.majAt C.basis (stdFrame C.H) v x y =
      ∑ c, ((C.wt c : ℕ) : ℂ)⁻¹ * (valDatum C).pairAt v (x.1 c) (y.1 c) := by
  have hs : IsSesq (fun v (x y : C.Forms) => ∑ c, ((C.wt c : ℕ) : ℂ)⁻¹ * (valDatum C).pairAt v (x.1 c) (y.1 c)) := by
    intro v
    refine ⟨fun x x' y => ?_, fun x y y' => ?_, fun a x y => ?_, fun a x y => ?_⟩
    · rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← mul_add, ← GSD.pairAt_add_left]
      rfl
    · rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← mul_add, ← GSD.pairAt_add_right]
      rfl
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [mul_left_comm, ← GSD.pairAt_smul_left]
      rfl
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [mul_left_comm, ← GSD.pairAt_smul_right]
      rfl
  have hg : gramOf C.basis (fun (x y : C.Forms) => ∑ c, ((C.wt c : ℕ) : ℂ)⁻¹ * (valDatum C).pairAt v (x.1 c) (y.1 c)) =
      C.H.map v.embedding := by
    ext a a'
    simp only [gramOf, Matrix.of_apply, Matrix.map_apply, CSD.H, CSD.csum, map_sum, map_mul, map_inv₀, map_natCast]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    exact ((valDatum C).pairAt_of_rat v _ _ fun i => C.basis_rat hb a c i).symm
  rw [sesq_eq_sum (isSesq_maj C.basis (stdFrame C.H)) C.basis v x y, sesq_eq_sum hs C.basis v x y, gramOf_maj, hg]
  have := (frameOfSpec _ _ (hp v)).2
  unfold metOf at this
  unfold stdFrame
  rw [this]

end Metric

section Forget

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}
  {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β] {Λ : β → LevFam X.E X.K n SG} {Θ : β → LevQFam X.E X.K n Q}
  (pref : DecoF X.E n ST SG Q → Prop) (lam : X.Tau → DomWeight n) {Λ₀ : LevFam X.E X.K n SG}

variable (ST Λ₀) in

abbrev base : GSD X.K := formGSD (roundPk X lam fun d : DecoSet X.E n ST SG => d.1.Lsh) Λ₀

def down (hΛ : ∀ b, Λ b = Λ₀) (b : β) : (stepY ST y β Λ Θ pref).G b →* FormG Λ₀ where
  toFun g := (g.1, ⟨g.2.1.1, hΛ b ▸ g.2.1.2⟩)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem deco_smul (hΛ : ∀ b, Λ b = Λ₀) (b : β) (g : (stepY ST y β Λ Θ pref).G b) (p : (stepY ST y β Λ Θ pref).D b) :
    (g • p).1.1.deco = down pref hΛ b g • p.1.1.deco := rfl

theorem chr_eq_one {Θ' : LevQFam X.E X.K n Q} (h : Θ' = LevQFam.top X.E X.K n Q) (c : Θ'.grp) : Θ'.chr c = 1 := by
  subst h
  exact LevQFam.top_chr c

theorem mem_grp {Θ' : LevQFam X.E X.K n Q} (h : Θ' = LevQFam.top X.E X.K n Q) (c : GLQ X.E n Q) : c ∈ Θ'.grp := by
  subst h
  exact (Subgroup.mem_pi _).2 fun _ _ => Subgroup.mem_top _

theorem chr_congr {Λ' : LevFam X.E X.K n SG} (h : Λ' = Λ₀) (a : Λ'.grp) : Λ'.chr a = Λ₀.chr ⟨a.1, h ▸ a.2⟩ := by
  subst h
  rfl

theorem rho_eq (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) (b : β) (g : (stepY ST y β Λ Θ pref).G b) :
    (stepY ST y β Λ Θ pref).rho X.emb lam b g = (base ST lam Λ₀).ρ (down pref hΛ b g) := by
  have h : (stepY ST y β Λ Θ pref).chr b g = Λ₀.chr (down pref hΛ b g).2 := by
    show (Λ b).chr g.2.1 * (Θ b).chr g.2.2 = _
    rw [chr_eq_one (hΘ b), mul_one, chr_congr (hΛ b)]
    rfl
  show (((stepY ST y β Λ Θ pref).chr b g : X.Kˣ) : X.K) • rhoVr X.emb lam ((stepY ST y β Λ Θ pref).gam b g) = _
  rw [h]
  rfl

theorem form_smul (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) (φ : (base ST lam Λ₀).EqFun) (b : β)
    (g : (stepY ST y β Λ Θ pref).G b) (p : (stepY ST y β Λ Θ pref).D b) :
    φ.1 (g • p).1.1.deco = (stepY ST y β Λ Θ pref).rho X.emb lam b g (φ.1 p.1.1.deco) := by
  rw [rho_eq pref lam hΛ hΘ]
  exact φ.2 (down pref hΛ b g) p.1.1.deco

theorem pt_ext (hy : ∀ N, y.ys N = {∅}) {p q : PtY ST SG Q y} (h : p.1.1 = q.1.1) : p = q := by
  have h1 := p.2
  have h2 := q.2
  rw [hy, Set.mem_singleton_iff] at h1 h2
  exact Subtype.ext (Prod.ext h (h1.trans h2.symm))

theorem exists_lift (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) (b : β)
    (p q : (stepY ST y β Λ Θ pref).D b) (g₀ : FormG Λ₀) (h : g₀ • p.1.1.deco = q.1.1.deco) :
    ∃ g : (stepY ST y β Λ Θ pref).G b, down pref hΛ b g = g₀ ∧ g • p = q := by
  obtain ⟨c, hc⟩ := GlobalTheory.FramedForms.exists_smul_of_deco_eq
    (p := ((g₀.1, g₀.2.1, 1) : UF X.E n × GLG X.E n SG × GLQ X.E n Q) • p.1.1) (q := q.1.1) h
  refine ⟨(g₀.1, ⟨g₀.2.1, (hΛ b).symm ▸ g₀.2.2⟩, ⟨c, mem_grp (hΘ b) c⟩), rfl, pt_ext hy ?_⟩
  rw [hc, smul_smul]
  simp only [Prod.mk_mul_mk, one_mul, mul_one]
  rfl

theorem exists_pt (hy : ∀ N, y.ys N = {∅}) (d : DecoSet X.E n ST SG) : ∃ p : PtY ST SG Q y, p.1.1.deco = d := by
  obtain ⟨γ, -, hγ⟩ := GlobalTheory.SemilocalBasis.exists_equiv X.E n Q d.1.N d.2.lat
  exact ⟨⟨(⟨(d, fun _ => γ), fun P x => hγ P.1 P.2 x⟩, ∅), by rw [hy]; rfl⟩, rfl⟩

theorem card_stab (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) (b : β)
    (p : (stepY ST y β Λ Θ pref).D b) :
    Nat.card (MulAction.stabilizer ((stepY ST y β Λ Θ pref).G b) p) =
      Nat.card (MulAction.stabilizer (FormG Λ₀) p.1.1.deco) := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun g => ⟨down pref hΛ b g.1, (deco_smul pref hΛ b g.1 p).symm.trans (congrArg (fun q => q.1.1.deco) g.2)⟩) ⟨?_, ?_⟩)
  · intro g g' h
    have h1 : g.1.1 = g'.1.1 := congrArg (fun a => a.1.1) h
    have h2 : (g.1⁻¹ * g'.1) = 1 := stepY_eq_one y β Λ Θ pref b _ p (g⁻¹ * g').2 (by
      show g.1.1⁻¹ * g'.1.1 = 1
      rw [h1, inv_mul_cancel])
    exact Subtype.ext (inv_mul_eq_one.1 h2)
  · intro g₀
    obtain ⟨g, h1, h2⟩ := exists_lift pref hy hΛ hΘ b p p g₀.1 g₀.2
    exact ⟨⟨g, h2⟩, Subtype.ext h1⟩

def clMap (c : (stepY ST y β Λ Θ pref).Cl) : (base ST lam Λ₀).Cl :=
  (base ST lam Λ₀).cls ((stepY ST y β Λ Θ pref).rep c).1.1.deco

theorem clMap_cl (hΛ : ∀ b, Λ b = Λ₀) (b : β) (p : (stepY ST y β Λ Θ pref).D b) :
    clMap (Λ₀ := Λ₀) pref lam ((stepY ST y β Λ Θ pref).cl b p) = (base ST lam Λ₀).cls p.1.1.deco := by
  conv_rhs => rw [← (stepY ST y β Λ Θ pref).mv_smul b p, deco_smul pref hΛ]
  exact ((base ST lam Λ₀).cls_smul _ _).symm

theorem clMap_bijective [Unique β] (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀)
    (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) :
    Function.Bijective (clMap (y := y) (Λ := Λ) (Θ := Θ) (Λ₀ := Λ₀) pref lam) := by
  refine ⟨?_, fun c₀ => ?_⟩
  · rintro ⟨b, q⟩ ⟨b', q'⟩ h
    obtain rfl : b = b' := Subsingleton.elim _ _
    obtain ⟨g₀, hg⟩ := ((base ST lam Λ₀).cls_eq_iff _ _).1 h
    obtain ⟨g, -, h2⟩ := exists_lift pref hy hΛ hΘ b _ _ g₀ hg
    congr 1
    rw [← (stepY ST y β Λ Θ pref).rp_spec b q, ← (stepY ST y β Λ Θ pref).rp_spec b q']
    exact Quotient.sound ⟨g, h2⟩
  · induction c₀ using Quotient.inductionOn' with
    | h d =>
      obtain ⟨p, rfl⟩ := exists_pt (Q := Q) hy d
      exact ⟨(stepY ST y β Λ Θ pref).cl default p, clMap_cl pref lam hΛ default p⟩

def clEquiv [Unique β] (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) :
    (stepY ST y β Λ Θ pref).Cl ≃ (base ST lam Λ₀).Cl :=
  Equiv.ofBijective _ (clMap_bijective pref lam hy hΛ hΘ)

def sec [Unique β] (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) :
    (base ST lam Λ₀).Sec where
  rep c := ((stepY ST y β Λ Θ pref).rep ((clEquiv pref lam hy hΛ hΘ).symm c)).1.1.deco
  spec c := (clEquiv pref lam hy hΛ hΘ).apply_symm_apply c

def formMap (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q)
    (h : ((stepY ST y β Λ Θ pref).fam X.emb lam).Ok) :
    (base ST lam Λ₀).EqFun →ₗ[X.K] (stepY ST y β Λ Θ pref).FormsK X.emb lam h where
  toFun φ := ⟨fun c => φ.1 ((stepY ST y β Λ Θ pref).rep c).1.1.deco, fun c g =>
    (form_smul pref lam hΛ hΘ φ c.1 g.1 _).symm.trans (congrArg (fun q => φ.1 q.1.1.deco) g.2)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem formMap_bijective [Unique β] (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀)
    (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) (h : ((stepY ST y β Λ Θ pref).fam X.emb lam).Ok) (h₀ : (base ST lam Λ₀).Ok) :
    Function.Bijective (formMap pref lam hΛ hΘ h) := by
  refine ⟨fun φ ψ e => ?_, fun f => ?_⟩
  · apply ((base ST lam Λ₀).resOf h₀ (sec pref lam hy hΛ hΘ)).injective
    apply Subtype.ext
    funext c
    exact congrFun (congrArg Subtype.val e) ((clEquiv pref lam hy hΛ hΘ).symm c)
  · let f₀ : ((base ST lam Λ₀).toCSDOf h₀ (sec pref lam hy hΛ hΘ)).Forms :=
      ⟨fun c => f.1 ((clEquiv pref lam hy hΛ hΘ).symm c), fun c g₀ => by
        obtain ⟨g, h1, h2⟩ := exists_lift pref hy hΛ hΘ _ _ _ g₀.1 g₀.2
        have h3 := f.2 ((clEquiv pref lam hy hΛ hΘ).symm c) ⟨g, h2⟩
        have h4 := rho_eq pref lam hΛ hΘ _ g
        rw [h1] at h4
        exact (LinearMap.congr_fun h4 _).symm.trans h3⟩
    refine ⟨((base ST lam Λ₀).resOf h₀ (sec pref lam hy hΛ hΘ)).symm f₀, Subtype.ext (funext fun c => ?_)⟩
    obtain ⟨c₀, rfl⟩ := (clEquiv pref lam hy hΛ hΘ).symm.surjective c
    exact congrFun (congrArg Subtype.val
      (((base ST lam Λ₀).resOf h₀ (sec pref lam hy hΛ hΘ)).apply_symm_apply f₀)) c₀

def formEquiv [Unique β] (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀)
    (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) (h : ((stepY ST y β Λ Θ pref).fam X.emb lam).Ok) (h₀ : (base ST lam Λ₀).Ok) :
    (base ST lam Λ₀).EqFun ≃ₗ[X.K] (stepY ST y β Λ Θ pref).FormsK X.emb lam h :=
  LinearEquiv.ofBijective _ (formMap_bijective pref lam hy hΛ hΘ h h₀)

end Forget

section Zero

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {G : ChGlob X R.m} {m2 : ℕ} (Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word)

theorem m_pos (R : Ranks) : 0 < R.m := lt_of_lt_of_le (by norm_num) R.two_le_m

theorem lamT_eq (j : ℕ) : lamT (W.hc u) j = W.lamTrue u j := rfl

variable (sel mu cst) in
theorem ysAt_zero (N : Submodule (𝓞 X.E) (Sp X.E (R.N 0))) : (ysAt R sel mu cst 0).ys N = {∅} := by
  have h : ¬ (0 + 1 = R.m) := by have := R.two_le_m; omega
  unfold ysAt
  rw [if_neg h]
  rfl

@[reducible] def idxUnique (hL : L.Ok Ch sel mu cst G m2) : Unique (Idx sel mu L 0) where
  default := ⟨some hL.zero_uniq.choose, by simpa using m_pos R⟩
  uniq := by
    rintro ⟨_ | b, hb⟩
    · exact absurd (hb.2 (m_pos R)) (by simp)
    · exact Subtype.ext (congrArg some (hL.zero_uniq.choose_spec b))

theorem levGAt_zero (hL : L.Ok Ch sel mu cst G m2) (b : Idx sel mu L 0) : levGAt sel mu L Tp 0 b = colLev Ch 0 := by
  obtain ⟨_ | b, hb⟩ := b
  · exact absurd (hb.2 (m_pos R)) (by simp)
  · exact hL.zero_G b

theorem levQAt_zero (hL : L.Ok Ch sel mu cst G m2) (b : Idx sel mu L 0) :
    levQAt sel mu L Tp 0 b = LevQFam.top X.E X.K (R.N 0) _ := by
  obtain ⟨_ | b, hb⟩ := b
  · exact absurd (hb.2 (m_pos R)) (by simp)
  · exact hL.zero_Q b

def clZero (hL : L.Ok Ch sel mu cst G m2) : (stepAt sel mu cst L Tp u 0).Cl ≃ (colGSD W Ch u 0).Cl :=
  letI := idxUnique hL
  clEquiv (Tp.pref u 0) (lamT (W.hc u) 0) (ysAt_zero sel mu cst) (levGAt_zero Tp hL) (levQAt_zero Tp hL)

def colZero (hX : X.Ok) (hL : L.Ok Ch sel mu cst G m2) (h : ((stepAt sel mu cst L Tp u 0).fam X.emb (lamT (W.hc u) 0)).Ok) :
    MfV W Ch u ≃ₗ[X.K] (stepAt sel mu cst L Tp u 0).FormsK X.emb (lamT (W.hc u) 0) h :=
  letI := idxUnique hL
  formEquiv (Tp.pref u 0) (lamT (W.hc u) 0) (ysAt_zero sel mu cst) (levGAt_zero Tp hL) (levQAt_zero Tp hL) h
    (colOk W Ch hX u 0)

variable (hX : X.Ok) (hL : L.Ok Ch sel mu cst G m2) (h : ((stepAt sel mu cst L Tp u 0).fam X.emb (lamT (W.hc u) 0)).Ok)

variable (rho : ∀ i (b : Idx sel mu L i), (stepAt sel mu cst L Tp u i).D b → ℂ)
  (rho' : ∀ i (b : Idx sel mu L (i + 1)), (stepAt sel mu cst L Tp u (i + 1)).D b → ℂ) (cD : X.Tau → ℂ)
  (Th : ∀ i (b : Idx sel mu L i) (b' : Idx sel mu L (i + 1)), (stepAt sel mu cst L Tp u i).D b →
    (stepAt sel mu cst L Tp u (i + 1)).D b' → Formalism.L2.Ker.VCx X.Tau (R.N i) (R.N (i + 1)) → ℂ)
  (xi0 : X.E) (du : ℕ) (Ds Gp : ℝ) (σ : X.K →+* ℂ)

theorem embF_injective {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι]
    {n : ℕ} (T : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n) (h : (T.fam emb lam).Ok) :
    Function.Injective (T.embF emb σ lam h) :=
  inj_of_li σ _ (T.hlat emb lam h).b (T.lawBasis_of_ok emb σ lam h).1

theorem embF_mem_Fi {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι]
    {n : ℕ} (T : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n) (h : (T.fam emb lam).Ok)
    (x : T.FormsK emb lam h) : T.embF emb σ lam h x ∈ T.Fi emb σ lam := by
  rw [← (T.lawBasis_of_ok emb σ lam h).2]
  exact mem_span_basis_image σ (T.hlat emb lam h).b _ x

end Zero

end GlobalTheory.Mem.Col2.StepZero
