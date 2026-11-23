import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDblClosed
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SeeSaw.GModel
variable {D : D7} {c : Comm D} {v : VCom c}

def matM (G : GLoc v) (j a : ℕ) (ha : j + a = G.s + 1) :
    GA D (c.V j) →* Matrix (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin a) (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin a) G.k where
  toFun g := (G.FY j a ha).γ * (mt (c.V j) g).map G.q.pr * (G.FY j a ha).β
  map_one' := by simp [Formalism.L2.Theta.mt, (G.FY j a ha).γβ]
  map_mul' g h := by
    have : mt (c.V j) (g * h) = mt (c.V j) g * mt (c.V j) h := by simp [Formalism.L2.Theta.mt]
    rw [this, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (G.FY j a ha).β, (G.FY j a ha).βγ, Matrix.one_mul]

theorem mat_iff (G : GLoc v) (j a : ℕ) (ha : j + a = G.s + 1) (g : GA D (c.V j)) (x) :
    G.Mat j a ha g x ↔ x = (matM G j a ha).toHomUnits g := by
  unfold GLoc.Mat
  constructor
  · intro h
    apply Units.ext
    change _ = (G.FY j a ha).γ * (mt (c.V j) g).map G.q.pr * (G.FY j a ha).β
    rw [h]
    simp only [Matrix.mul_assoc]
    rw [(G.FY j a ha).γβ, Matrix.mul_one, ← Matrix.mul_assoc, (G.FY j a ha).γβ, Matrix.one_mul]
  · rintro rfl
    change _ = _ * ((G.FY j a ha).γ * (mt (c.V j) g).map G.q.pr * (G.FY j a ha).β) * _
    simp only [Matrix.mul_assoc]
    rw [(G.FY j a ha).βγ, Matrix.mul_one, ← Matrix.mul_assoc, (G.FY j a ha).βγ, Matrix.one_mul]

theorem glam_unique {n : ℕ} (G : Fin n → GLoc v) (j : ℕ) (g : GA D (c.V j)) {a a' : ℂ} (h : GLam G j g a) (h' : GLam G j g a') :
    a = a' := by
  obtain ⟨b, hb, x, hx, rfl⟩ := h
  obtain ⟨b', hb', x', hx', rfl⟩ := h'
  obtain rfl : b = b' := funext fun i => by have := hb i; have := hb' i; omega
  refine Finset.prod_congr rfl fun i _ => ?_
  have : x i = x' i := Subtype.ext (((mat_iff _ _ _ _ _ _).1 (hx i)).trans ((mat_iff _ _ _ _ _ _).1 (hx' i)).symm)
  rw [this]

theorem glam_exists {n : ℕ} {G : Fin n → GLoc v} (P : GPin G) (j : ℕ) (hj : j < D.R.m) (g : GA D (c.V j)) (hg : g ∈ v.JG j) :
    ∃ a, a ≠ 0 ∧ GLam G j g a := by
  have hb : ∀ i, j + ((G i).s + 1 - j) = (G i).s + 1 := fun i => by have := (G i).hs; omega
  refine ⟨_, ?_, fun i => (G i).s + 1 - j, hb, fun i => ⟨_, ((P.lev j hj g).1 hg).2 i _ (hb i) _ ((mat_iff _ _ _ _ _ _).2 rfl)⟩,
    fun i => (mat_iff _ _ _ _ _ _).2 rfl, rfl⟩
  exact Finset.prod_ne_zero_iff.2 fun i _ => Units.ne_zero _

theorem glam_mul {n : ℕ} (G : Fin n → GLoc v) (j : ℕ) {g g' : GA D (c.V j)} {a a' : ℂ} (h : GLam G j g a) (h' : GLam G j g' a') :
    GLam G j (g * g') (a * a') := by
  obtain ⟨b, hb, x, hx, rfl⟩ := h
  obtain ⟨b', hb', x', hx', rfl⟩ := h'
  obtain rfl : b = b' := funext fun i => by have := hb i; have := hb' i; omega
  refine ⟨b, hb, fun i => x i * x' i, fun i => (mat_iff _ _ _ _ _ _).2 ?_, ?_⟩
  · rw [map_mul, ← (mat_iff _ _ _ _ _ _).1 (hx i), ← (mat_iff _ _ _ _ _ _).1 (hx' i)]; rfl
  · rw [← Finset.prod_mul_distrib]; simp

theorem exists_foldr (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {ι : Type} (e : ι → WO S T →₀ ℂ) (l : List ι) :
    ∃ d : WO S T →₀ ℂ, ∀ f, comb ψ S T d f = l.foldr (fun i f' => comb ψ S T (e i) f') f := by
  induction l with
  | nil =>
    refine ⟨Finsupp.single 0 1, fun f => ?_⟩
    funext w
    simp [comb, Finsupp.support_single_ne_zero, heisO, symplOH, symplO, hO]
  | cons i l ih =>
    obtain ⟨d, hd⟩ := ih
    obtain ⟨d', -, h'⟩ := (GlobalTheory.HeisComb.main D ψ S T).1 (e i) d
    exact ⟨d', fun f => by rw [h', hd]; rfl⟩

def reG (v : VCom c) (gP : Finset (GlobalTheory.FinPl.Pl D)) (JG : ∀ j, Subgroup (GA D (c.V j))) (eG : ∀ j, WO (c.V j) (c.V (j + 1)) →₀ ℂ)
    (eGT : ∀ j, j + 2 * 0 + 2 = D.R.m → WO (c.V (j + 1)) c.T →₀ ℂ) (dG : ∀ j, WO (c.X j) (c.X (j + 1)) →₀ ℂ) : VCom c :=
  { v with gP := gP, JG := JG, eG := eG, eGT := eGT, dG := dG }

def move (G : GLoc v) (gP JG eG eGT dG) : GLoc (reG v gP JG eG eGT dG) := { G with }

theorem exists_pin {n : ℕ} (G : Fin n → GLoc v) (inj : Function.Injective fun i => (G i).q.v) :
    ∃ gP JG eG eGT dG, GPin fun i => move (G i) gP JG eG eGT dG := by
  classical
  choose eG heG using fun j => exists_foldr c.ψ (c.V j) (c.V (j + 1)) (fun i => (G i).eg j) (List.finRange n)
  choose dG hdG using fun j => exists_foldr c.ψ (c.X j) (c.X (j + 1)) (fun i => (G i).cg j) (List.finRange n)
  have hT : ∀ j (_ : j + 2 * 0 + 2 = D.R.m) i, ∃ e : WO (c.V (j + 1)) c.T →₀ ℂ, HEq e (G i).egT := fun j h i => by
    obtain rfl : j = (G i).s := by have := (G i).hs; omega
    exact ⟨_, HEq.rfl⟩
  choose e he using hT
  choose eGT heGT using fun j h => exists_foldr c.ψ (c.V (j + 1)) c.T (e j h) (List.finRange n)
  let gP : Finset (GlobalTheory.FinPl.Pl D) := Finset.univ.image fun i => (G i).q.v
  refine ⟨gP, fun j => GlobalTheory.FinPl.grpAt (c.V j) (· ∈ gP) ⊓ ⨅ i, ⨅ a, ⨅ ha : j + a = (G i).s + 1,
    (((G i).S.T (Fin D.R.t)).lev j a ha).J.comap (matM (G i) j a ha).toHomUnits, eG, eGT, dG, inj, fun p => ?_, fun j _ g => ?_,
    fun j _ f _ => heG j f, fun j h => ⟨e j h, he j h, fun f _ => heGT j h f⟩, fun j _ f _ => hdG j f⟩
  · change p ∈ gP ↔ ∃ i, p = (G i).q.v
    simp [gP, eq_comm]
  · change g ∈ _ ⊓ _ ↔ g ∈ GlobalTheory.FinPl.grpAt (c.V j) (· ∈ gP) ∧ ∀ i a ha x, (G i).Mat j a ha g x → x ∈ (((G i).S.T (Fin D.R.t)).lev j a ha).J
    simp only [Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap, mat_iff, forall_eq]

section Rel
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_gLoc (v : VCom c) [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (unitVol : IsUnitVol ν) (q : GlobalTheory.FinPl.SplitPt D k)
    (unit : q.UnitAA) (s : ℕ) (hs : s + 1 + 1 = D.R.m) (S : SymData k s D.R.k) (char : (ofSplit q).IsChar c.ψ S.ψ)
    (FX : ∀ j, j ≤ s + 1 → GlobalTheory.LocMod.Frame k (c.X j).rank (XIx (Fin D.R.k) (Fin D.R.t) j))
    (FT : GlobalTheory.LocMod.Frame k c.T.rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2)))
    (FM : GlobalTheory.LocMod.Frame k (c.X (s + 1 + 1)).rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit))
    (a₀ : k) (hc : valuation k a₀ = 1) (hxi : valuation k (ofSplit q).xi = 1)
    (hz_unit : ∀ j ρ h, valuation k ((ofSplit q).hz (c.B j ρ h)) = 1) (z₀ : Fin c.Lz.rank → k)
    (last : FM.β = fromCols ((c.oT (s + 1 + 1) hs).iA.map (ofSplit q).pr * FT.β)
      (Matrix.of fun r _ => ((c.oT (s + 1 + 1) hs).iB.map (ofSplit q).pr *ᵥ z₀) r))
    (tau : ∀ h, (v.τ s h).map (ofSplit q).pr *ᵥ z₀ = (-((ofSplit q).xi * a₀)) • fun i => (ofSplit q).pr ((c.bes s 0 h).ζ i))
    (latX : ∀ j hj, IntIn q (c.X j) (FX j hj) (c.x j).L) (latM : IntIn q (c.X (s + 1 + 1)) FM (c.x (s + 1 + 1)).L)
    (hLat : ∀ (V : HSp D) (Y : Type) [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y), ∃ L, IsSelfDualC V L ∧ IntIn q V F L)
    (hComb : ∀ (V W : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
      (F' : GlobalTheory.LocMod.Frame k V.rank Y') (F : GlobalTheory.LocMod.Frame k W.rank Y) (Φ : SB (Matrix Y Y' k)),
      ∃ e, (ofSplit q).IsCombAt c.ψ F' F e Φ.1) :
    ∃ N NT, (∀ j, j < D.R.m → IsSelfDualC (c.V j) (N j)) ∧ IsSelfDualC c.T NT ∧ Nonempty (GLoc { v with N := N, NT := NT }) := by
  set p := ofSplit q with hp
  have hC : ∀ (V W : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
      (F' : GlobalTheory.LocMod.Frame k V.rank Y') (F : GlobalTheory.LocMod.Frame k W.rank Y) (Ξ : Matrix Y Y' k → ℂ), ∃ e, p.IsCombAt c.ψ F' F e Ξ := by
    intro V W Y Y' _ _ _ _ F' F Ξ
    by_cases h : Ξ ∈ SB (Matrix Y Y' k)
    · exact hComb V W Y Y' F' F ⟨Ξ, h⟩
    · exact ⟨0, by simp, fun _ _ _ Φ _ e => absurd (e ▸ Φ.2) h⟩
  have hx : p.xi ≠ 0 := Witness.xi_ne p
  have hc0 : a₀ ≠ 0 := by rintro rfl; simp at hc
  let sc : ℕ → k := fun j => a₀ * p.xi ^ (j / 2) / p.xi ^ (s / 2)
  have sc0 : ∀ j, sc j ≠ 0 := fun j => div_ne_zero (mul_ne_zero hc0 (pow_ne_zero _ hx)) (pow_ne_zero _ hx)
  have hodd := S.odd
  let Q : ∀ j a, j + a = s + 1 → GlobalTheory.LocMod.Frame k (c.V j).rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin a) → Prop := fun j =>
    match j with
    | 0 => fun _ _ _ => True
    | j + 1 => fun a ha F => ∀ ρ h, p.IsJacFrame (c.J j ρ h) (sc j) (p.hz (c.B j ρ h)) (FX (j + 1) (by omega)) F
  have hFY : ∀ j a (ha : j + a = s + 1), ∃ F : GlobalTheory.LocMod.Frame k (c.V j).rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin a),
      (∀ ρ h, p.IsBesFrame (c.B j ρ h) (sc j) (FX j (by omega)) F) ∧ Q j a ha F := by
    intro j a ha
    by_cases hj : j % 2 = 0
    · obtain ⟨ρ, rfl⟩ : ∃ ρ, a = 2 * ρ + 1 := ⟨a / 2, by omega⟩
      have h : j + 2 * ρ + 2 = D.R.m := by omega
      obtain ⟨F, hF⟩ := Witness.exists_bes p (c.B j ρ h) (sc0 j) (FX j (by omega))
      refine ⟨F, fun ρ' h' => ?_, ?_⟩
      · obtain rfl : ρ' = ρ := by omega
        exact hF
      · cases j with
        | zero => trivial
        | succ j => intro ρ' h'; omega
    · obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      obtain ⟨ρ, rfl⟩ : ∃ ρ, a = 2 * ρ := ⟨a / 2, by omega⟩
      have h : j + 2 * ρ + 2 = D.R.m := by omega
      obtain ⟨F, hF⟩ := Witness.exists_jac p (c.J j ρ h) (sc0 j) (Witness.hz_ne p (c.B j ρ h)) (FX (j + 1) (by omega))
      refine ⟨F, fun ρ' h' => by omega, fun ρ' h' => ?_⟩
      obtain rfl : ρ' = ρ := by omega
      exact hF
  choose FY hB hJ using hFY
  obtain ⟨NT, hNT, latT⟩ := hLat c.T _ FT
  have hN : ∀ j, ∃ L : GlobalTheory.FinPl.Lat (c.V j), (j < D.R.m → IsSelfDualC (c.V j) L) ∧ ∀ a ha, IntIn q (c.V j) (FY j a ha) L := by
    intro j
    by_cases hj : j ≤ s + 1
    · obtain ⟨a, ha⟩ : ∃ a, j + a = s + 1 := ⟨s + 1 - j, by omega⟩
      obtain ⟨L, h1, h2⟩ := hLat (c.V j) _ (FY j a ha)
      refine ⟨L, fun _ => h1, fun a' ha' => ?_⟩
      obtain rfl : a' = a := by omega
      exact h2
    · exact ⟨⊥, fun h => by omega, fun a ha => by omega⟩
  choose N sdN latY using hN
  have heg : ∀ j, ∃ e : WO (c.V j) (c.V (j + 1)) →₀ ℂ, ∀ a (H : j + a = s),
      p.IsCombAt c.ψ (FY j (a + 1) (by omega)) (FY (j + 1) a (by omega)) e ((S.T (Fin D.R.t)).Phi j a H) := by
    intro j
    by_cases hj : j ≤ s
    · obtain ⟨a, ha⟩ : ∃ a, j + a = s := ⟨s - j, by omega⟩
      obtain ⟨e, he⟩ := hC _ _ _ _ (FY j (a + 1) (by omega)) (FY (j + 1) a (by omega)) ((S.T (Fin D.R.t)).Phi j a ha)
      refine ⟨e, fun a' ha' => ?_⟩
      obtain rfl : a' = a := by omega
      exact he
    · exact ⟨0, fun a ha => by omega⟩
  choose eg eg_is using heg
  obtain ⟨egT, egT_is⟩ := hC _ _ _ _ (FY (s + 1) 0 rfl) FT (S.T (Fin D.R.t)).PhiTop
  have hcg : ∀ j, ∃ e : WO (c.X j) (c.X (j + 1)) →₀ ℂ, (∀ a (H : j + 1 + a = s),
      p.IsCombAt c.ψ (FX j (by omega)) (FX (j + 1) (by omega)) e ((S.T (Fin D.R.t)).entry S.ψ ν j a H 1 1)) ∧
      (∀ h : j = s, p.IsCombAt c.ψ (FX s (by omega)) (FX (s + 1) le_rfl) (h ▸ e)
        fun x₀ => (S.T (Fin D.R.t)).Psi 1 x₀ (S.y0 (Fin D.R.t))) ∧
      ∀ h : j = s + 1, p.IsCombAt c.ψ (FX (s + 1) le_rfl) FM (h ▸ e)
        ((S.T (Fin D.R.t)).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 (Fin D.R.t)))) := by
    intro j
    by_cases h1 : j + 1 ≤ s
    · obtain ⟨a, ha⟩ : ∃ a, j + 1 + a = s := ⟨s - (j + 1), by omega⟩
      obtain ⟨e, he⟩ := hC _ _ _ _ (FX j (by omega)) (FX (j + 1) (by omega)) ((S.T (Fin D.R.t)).entry S.ψ ν j a ha 1 1)
      refine ⟨e, fun a' ha' => ?_, fun h => by omega, fun h => by omega⟩
      obtain rfl : a' = a := by omega
      exact he
    by_cases h2 : j = s
    · subst h2
      obtain ⟨e, he⟩ := hC _ _ _ _ (FX j (by omega)) (FX (j + 1) le_rfl) fun x₀ => (S.T (Fin D.R.t)).Psi 1 x₀ (S.y0 (Fin D.R.t))
      exact ⟨e, fun a ha => by omega, fun _ => he, fun h => by omega⟩
    by_cases h3 : j = s + 1
    · subst h3
      obtain ⟨e, he⟩ := hC _ _ _ _ (FX (s + 1) le_rfl) FM
        ((S.T (Fin D.R.t)).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 (Fin D.R.t))))
      exact ⟨e, fun a ha => by omega, fun h => by omega, fun _ => he⟩
    · exact ⟨0, fun a ha => by omega, fun h => absurd h h2, fun h => absurd h h3⟩
  choose cg cg1 cg2 cg3 using hcg
  refine ⟨N, NT, sdN, hNT, ⟨⟨k, ν, unitVol, q, unit, s, hs, S, char, FX, FT, FM, FY, sc, fun j => ?_, fun j => ?_, hz_unit,
    fun j ρ h a ha => hB j a ha ρ h, fun j ρ h a ha => hJ (j + 1) a ha ρ h, z₀, last, fun h => ?_, latX, latM, latY, latT, eg, eg_is,
    egT, egT_is, cg, cg1, cg2 s rfl, cg3 (s + 1) rfl⟩⟩⟩
  · simp [sc, hc, hxi]
  · simp only [sc]
    rw [show (j + 1 + 1) / 2 = j / 2 + 1 by omega, pow_succ, ← hp]
    ring
  · have : sc s = a₀ := by simp only [sc]; field_simp
    rw [this]; exact tau h

end Rel

section Mu
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_det {a : Type} [Fintype a] [DecidableEq a] {g : GL a k} (hg : g ∈ KO k a) :
    valuation k ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = 1 := by
  have key : ∀ M : Matrix a a k, IntM M → valuation k M.det ≤ 1 := fun M hM => by
    have : M.det ∈ 𝒪[k] := by
      rw [Matrix.det_apply']
      exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => hM _ _)
    exact this
  have h1 := key _ (mem_KO.1 hg).1
  have h2 := key _ (mem_KO.1 hg).2
  have h3 : valuation k g.val.det * valuation k (g⁻¹).val.det = 1 := by
    rw [← map_mul, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, map_one]
  refine le_antisymm h1 ?_
  calc 1 = valuation k g.val.det * valuation k (g⁻¹).val.det := h3.symm
    _ ≤ valuation k g.val.det * 1 := by gcongr
    _ = _ := mul_one _

theorem iter_congr {r t : Type} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum k r) {μ μ' : ℕ → kˣ →* ℂˣ}
    (h : ∀ j, IsTame (μ j)) (h' : ∀ j, IsTame (μ' j)) (e : ∀ j (x : kˣ), valuation k (x : k) = 1 → μ j x = μ' j x) (j : ℕ) :
    P.iter t μ h j = P.iter t μ' h' j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [TypeDatum.iter_succ, TypeDatum.iter_succ, ih]
    generalize P.iter t μ' h' j = Q
    have : Q.stepLam t (μ (j + 1)) (h _) = Q.stepLam t (μ' (j + 1)) (h' _) := by
      refine MonoidHom.ext fun g => ?_
      change _ * (μ (j + 1) _)⁻¹ * μ (j + 1) _ = _ * (μ' (j + 1) _)⁻¹ * μ' (j + 1) _
      rw [e _ _ (val_det (Q.le_KO (Q.corner g).2)), e _ _ (val_det g.2.1)]
    unfold TypeDatum.step
    simp only [this]

theorem withMu_same {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (μ : ℕ → kˣ →* ℂˣ) (h : ∀ j, IsTame (μ j))
    (e : ∀ j (x : kˣ), valuation k (x : k) = 1 → μ j x = S.μ j x) :
    ((withMu S μ h).T t).lev = (S.T t).lev ∧ ((withMu S μ h).T t).Phi = (S.T t).Phi ∧ ((withMu S μ h).T t).PhiTop = (S.T t).PhiTop := by
  have hΦ : ∀ j, S.P.iterPhi t μ h j = S.P.iterPhi t S.μ S.tame j := fun j => by
    unfold TypeDatum.iterPhi
    rw [iter_congr S.P h S.tame e j]
    generalize S.P.iter t S.μ S.tame j = Q
    have : Q.rho (μ (j + 1)) = Q.rho (S.μ (j + 1)) := MonoidHom.ext fun g => by
      rw [TypeDatum.rho_apply, TypeDatum.rho_apply, e _ _ (val_det (Q.le_KO g.2))]
    unfold TypeDatum.Phi
    rw [this]
  refine ⟨?_, ?_, ?_⟩
  · funext j a ha
    change (S.P.iter t μ h j).toLevel.map _ = (S.P.iter t S.μ S.tame j).toLevel.map _
    rw [iter_congr S.P h S.tame e j]; rfl
  · funext j a ha
    change LatFrame.transport _ _ (S.P.iterPhi t μ h j) = LatFrame.transport _ _ (S.P.iterPhi t S.μ S.tame j)
    rw [hΦ]; rfl
  · change LatFrame.transport _ _ (S.P.iterPhi t μ h _) = LatFrame.transport _ _ (S.P.iterPhi t S.μ S.tame _)
    rw [hΦ]; rfl

end Mu

open MeasureTheory IsDedekindDomain NumberField Matrix ValuativeRel in
open scoped TensorProduct in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar in
variable {D : _root_.Formalism.BasicNotions.D7} {c : _root_.GlobalTheory.SeeSaw.Comm D} {v : _root_.GlobalTheory.SeeSaw.VCom c} in

theorem _root_.GlobalTheory.SeeSaw.GModel.phi_sb (G : _root_.GlobalTheory.SeeSaw.GLoc v) :
    (∀ j a H, (G.S.T (Fin D.R.t)).Phi j a H ∈
      _root_.GlobalTheory.SplitWeil.SB _) ∧
    (G.S.T (Fin D.R.t)).PhiTop ∈ _root_.GlobalTheory.SplitWeil.SB _ := by
  have hreg : (G.S.T (Fin D.R.t)).Regular := by
    unfold _root_.GlobalTheory.SymChain.SymData.T _root_.GlobalTheory.StepData.typeChain
    exact _root_.GlobalTheory.StepData.Chain.ofType_regular _ _ _ _ _
  obtain ⟨hstep, htop, -⟩ := hreg
  exact ⟨hstep, htop⟩

theorem volLast_ne (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) : Measure.map (c.jac j 0 h).d.emb0 (c.x (j + 1)).vol.μ ≠ 0 := by
  haveI := (c.x (j + 1)).vol.haar
  rw [Ne, Measure.map_eq_zero_iff (c.jac j 0 h).d.continuous_embed.measurable.aemeasurable]
  exact NeZero.ne _

def inv0 {S S₀ : HSp D} (d : HypDec S S₀ 0) : HypDec S₀ S 0 where
  e := 0
  e' := 0
  i₀ := d.q0
  ee := Subsingleton.elim _ _
  e'e' := Subsingleton.elim _ _
  e'e := Subsingleton.elim _ _
  iso := by
    have h : d.i₀ * d.q0 = 1 := by simpa [Matrix.mul_empty] using d.sum_eq_one_rat
    rw [← d.iso]
    calc _ = (d.i₀ * d.q0)ᴴ * S.gram * (d.i₀ * d.q0) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h]; simp
  i₀e := Subsingleton.elim _ _
  i₀e' := Subsingleton.elim _ _
  rank_add := by have := d.rank_add; omega

theorem haar_map {S S₀ : HSp D} (d : HypDec S S₀ 0) (μ : Measure (GA D S₀)) [μ.IsHaarMeasure] : (μ.map d.emb0).IsHaarMeasure := by
  have h1 : d.j0 * (inv0 d).j0 = 1 := show d.j0 * d.p0 = 1 by simpa [Matrix.mul_empty] using d.sum_eq_one
  have h2 : (inv0 d).j0 * d.j0 = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by have := d.rank_add; simp; omega)).1 h1
  have key : ∀ {A B : HSp D} (a : HypDec A B 0) (b : HypDec B A 0), a.j0 * b.j0 = 1 → ∀ g, a.emb0 (b.emb0 g) = g := by
    intro A B a b h g
    have e : mt A (a.emb0 (b.emb0 g)) = mt A g := by
      rw [← Matrix.mul_one (mt A (a.emb0 _)), ← h, ← Matrix.mul_assoc, a.wittDecomp_anisotropicEmbedding_inclAnisotropic, Matrix.mul_assoc, b.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc, h,
        Matrix.one_mul]
    exact Subtype.ext (Units.ext e)
  let φ : GA D S₀ ≃ₜ* GA D S :=
    { toFun := d.emb0, invFun := (inv0 d).emb0, left_inv := key _ _ h2, right_inv := key _ _ h1, map_mul' := map_mul _
      continuous_toFun := d.continuous_embed, continuous_invFun := (inv0 d).continuous_embed }
  exact φ.isHaarMeasure_map μ

end GlobalTheory.SeeSaw.GModel
end
