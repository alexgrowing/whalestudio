import CompanionTheory.AutomorphicTheory.JacobiDiagonalBounds.StarLoweringConstant
import CompanionTheory.AutomorphicTheory.JacobiDiagonalBounds.TieRad

namespace Formalism.FourierDecayAlt.P.NormalFormRelations

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.P.RuleGD

noncomputable section

section Gshift

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r)

theorem cG : L.G ∈ Subring.closure L.fns := Subring.mul_mem _ (Subring.mul_mem _ (cDr L) (cDrb L)) (cGG L)

theorem hat_G (X : A) (hX : X ∈ hats L) : ∃ X' ∈ hats L, X * L.G = L.G * X' := by
  have cGi : L.GGi * L.Drbi * L.Dri ∈ Subring.closure L.fns :=
    Subring.mul_mem _ (Subring.mul_mem _ (cGGi L) (cDrbi L)) (cDri L)
  have h1 : L.G * (L.GGi * L.Drbi * L.Dri) = 1 := by
    calc L.G * (L.GGi * L.Drbi * L.Dri) = L.Dr * (L.Drb * (L.GG * L.GGi) * L.Drbi) * L.Dri := by
          simp only [LevelData.G, mul_assoc]
      _ = 1 := by rw [L.GG_GGi, mul_one, Drb_Drbi, mul_one, Dr_Dri]
  have h2 : (L.GGi * L.Drbi * L.Dri) * L.G = 1 := by rw [(cl_comm L cGi (cG L)).eq, h1]
  have key : ∀ (Z : A) (a b c : A), Z * L.Dr = L.Dr * Z + a * L.Dr → Z * L.Drb = L.Drb * Z + b * L.Drb →
      Z * L.GG = L.GG * Z + c * L.GG → a ∈ Subring.closure L.fns → b ∈ Subring.closure L.fns →
      c ∈ Subring.closure L.fns → Z * L.G = L.G * Z + (a + b + c) * L.G := by
    intro Z a b c ha hb hc ma mb mc
    have e1 := (cl_comm L (cDr L) mb).eq
    have e2 := (cl_comm L (Subring.mul_mem _ (cDr L) (cDrb L)) mc).eq
    calc Z * L.G = (Z * L.Dr) * L.Drb * L.GG := by simp only [LevelData.G, mul_assoc]
      _ = L.Dr * (Z * L.Drb) * L.GG + a * L.G := by rw [ha]; simp only [LevelData.G, add_mul, mul_assoc]
      _ = L.Dr * L.Drb * (Z * L.GG) + (L.Dr * b) * L.Drb * L.GG + a * L.G := by
          rw [hb]; simp only [add_mul, mul_add, mul_assoc]
      _ = L.G * Z + (L.Dr * L.Drb * c) * L.GG + b * L.G + a * L.G := by
          rw [hc, e1]; simp only [LevelData.G, mul_add, mul_assoc]
      _ = _ := by rw [e2]; simp only [LevelData.G, add_mul, mul_assoc]; abel
  have z := (Subring.closure L.fns).zero_mem
  have o := (Subring.closure L.fns).one_mem
  have hG := gaugeConjugation A r L 1 L.G _ h1 h2 (fun x hx => (cl_comm L (clF L hx) (cG L)).eq)
    (fun l => by
      rw [key (L.p l) 1 0 0 (p_Dr L l) (by rw [zero_mul, add_zero]; exact comm_Drb L (L.p_cb l))
        (by rw [zero_mul, add_zero]; exact L.p_GG l) o z z]; simp)
    (fun l => by
      rw [key (L.pb l) 0 1 0 (by rw [zero_mul, add_zero]; exact comm_Dr L (L.pb_c l)) (pb_Drb L l)
        (by rw [zero_mul, add_zero]; exact L.pb_GG l) z o z]; simp)
    (by
      rw [key L.nab 0 0 (L.ζb * L.GGi) (by rw [zero_mul, add_zero]; exact comm_Dr L L.nab_c)
        (by rw [zero_mul, add_zero]; exact comm_Drb L L.nab_cb)
        (by rw [mul_assoc, L.GGi_GG, mul_one]; exact L.nab_GG) z z (Subring.mul_mem _ (cζb L) (cGGi L))]; simp)
    (by
      rw [key L.nabs 0 0 (-(L.ζ * L.GGi)) (by rw [zero_mul, add_zero]; exact comm_Dr L L.nabs_c)
        (by rw [zero_mul, add_zero]; exact comm_Drb L L.nabs_cb)
        (by rw [neg_mul, mul_assoc, L.GGi_GG, mul_one, ← sub_eq_add_neg]; exact L.nabs_GG) z z
        (Subring.neg_mem _ (Subring.mul_mem _ (cζ L) (cGGi L)))]; simp [sub_eq_add_neg])
  have fin : ∀ {Z Z' : A}, L.GGi * L.Drbi * L.Dri * Z * L.G = Z' → Z * L.G = L.G * Z' := fun {Z Z'} h => by
    rw [← h, ← mul_assoc, ← mul_assoc, h1, one_mul]
  rcases hX with (((⟨y, rfl⟩ | ⟨y, rfl⟩) | ⟨y, rfl⟩) | ⟨y, rfl⟩)
  · exact ⟨_, mA _, fin (hG y).1⟩
  · exact ⟨_, mR _, fin (hG y).2.1⟩
  · exact ⟨_, mAv _, fin (hG y).2.2.1⟩
  · exact ⟨_, mRv _, fin (hG y).2.2.2⟩

theorem hats_G (h : List A) (hh : ∀ a ∈ h, a ∈ hats L) :
    ∃ h' : List A, h'.length = h.length ∧ (∀ a ∈ h', a ∈ hats L) ∧ h.prod * L.G = L.G * h'.prod := by
  induction h with
  | nil => exact ⟨[], rfl, hh, by simp⟩
  | cons X h ih =>
    obtain ⟨h', hl, hh', e⟩ := ih fun a ha => hh a (List.mem_cons_of_mem _ ha)
    obtain ⟨X', hX', e'⟩ := hat_G L X (hh X List.mem_cons_self)
    refine ⟨X' :: h', by simp [hl], fun a ha => ?_, ?_⟩
    · rcases List.mem_cons.1 ha with rfl | ha
      · exact hX'
      · exact hh' a ha
    · rw [List.prod_cons, List.prod_cons, mul_assoc, e, ← mul_assoc, e', mul_assoc]

theorem hats_Gpow (s : ℕ) (h : List A) (hh : ∀ a ∈ h, a ∈ hats L) :
    ∃ h' : List A, h'.length = h.length ∧ (∀ a ∈ h', a ∈ hats L) ∧ h.prod * L.G ^ s = L.G ^ s * h'.prod := by
  induction s with
  | zero => exact ⟨h, rfl, hh, by simp⟩
  | succ s ih =>
    obtain ⟨h', hl, hh', e⟩ := ih
    obtain ⟨h'', hl', hh'', e'⟩ := hats_G L h' hh'
    exact ⟨h'', hl'.trans hl, hh'', by rw [pow_succ, ← mul_assoc, e, mul_assoc, e', mul_assoc]⟩

theorem star_prod_comm [StarRing A] {ι : Type} (f g : ι → A) (h : ∀ i, star (f i) = g i)
    (hc : ∀ i j, Commute (g i) (g j)) (l : List ι) : star (l.map f).prod = (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, star_mul, ih, h]
    refine (Commute.list_prod_left _ _ fun x hx => ?_).eq
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact hc i a

end Gshift

section model

variable {P : M.Par} {L : LevelData (MA.A P (MA.DQ P)) P.r}

theorem sc_central (w : (MA.DQ P).Pr) (X : MA.A P (MA.DQ P)) (h : ∀ i j, ∃ z : ℂ, X i j = algebraMap ℂ _ z) :
    Commute X (MA.sc P (MA.DQ P) w) := by
  show X * _ = _ * X
  ext i j : 2
  rw [MA.sc, Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  obtain ⟨z, hz⟩ := h i j
  rw [hz, Algebra.commutes]

theorem fns_sc (hM : MA.IsModelLevel P (MA.DQ P) L) {f : MA.A P (MA.DQ P)} (hf : f ∈ L.fns) :
    ∃ w, f = MA.sc P (MA.DQ P) w := by
  obtain ⟨-, -, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, hg, hgi, -⟩ := hM
  simp only [LevelData.fns, Set.mem_union, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | h)
  · exact ⟨_, congrFun hc l⟩
  · exact ⟨_, congrFun hci l⟩
  · exact ⟨_, congrFun hcb l⟩
  · exact ⟨_, congrFun hcbi l⟩
  · rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [⟨_, hz⟩, ⟨_, hzi⟩, ⟨_, hzb⟩, ⟨_, hzbi⟩, ⟨_, hg⟩, ⟨_, hgi⟩]

theorem kap_diag (g : M.Ty P → ℂ) :
    MA.kap P (MA.DQ P) g = Matrix.diagonal fun π => algebraMap ℂ (MA.DQ P).Pr (g π) := rfl

theorem kap_central (g : M.Ty P → ℂ) (i j : M.Ty P) : ∃ z : ℂ, MA.kap P (MA.DQ P) g i j = algebraMap ℂ _ z := by
  rw [kap_diag, Matrix.diagonal_apply]
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨0, (map_zero _).symm⟩

theorem SS_central (l : ℕ) (i j : M.Ty P) : ∃ z : ℂ, MA.SS P (MA.DQ P) l i j = algebraMap ℂ _ z := by
  simp only [MA.SS, Matrix.of_apply]
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨0, (map_zero _).symm⟩

theorem star_kap (g : M.Ty P → ℂ) : star (MA.kap P (MA.DQ P) g) = MA.kap P (MA.DQ P) (star g) := by
  rw [kap_diag, kap_diag, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  congr 1
  funext π
  exact (algebraMap_star_comm (g π)).symm

theorem model_star_c (hM : MA.IsModelLevel P (MA.DQ P) L) (l : Fin P.r) :
    star (L.p l) = -L.pb l ∧ star (L.c l) = L.cb l ∧ star (L.ci l) = L.cbi l := by
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, -⟩ := hM
  refine ⟨?_, ?_, ?_⟩
  · rw [hp, hpb, MA.pA, MA.pbA, sc_star, MA.sc, MA.sc, ← map_neg]
    congr 1
    refine Prod.ext rfl ?_
    show MulOpposite.op _ = -MulOpposite.op (-_)
    rw [← MulOpposite.op_neg, neg_neg]
    rfl
  · rw [hc, hcb, MA.cA, sc_star]; rfl
  · rw [hci, hcbi, MA.ciA, sc_star]; rfl

theorem model_star_D (hM : MA.IsModelLevel P (MA.DQ P) L) : star L.Dr = L.Drb ∧ star L.Dri = L.Drbi := by
  constructor
  · rw [LevelData.Dr, LevelData.Drb, List.ofFn_eq_map, List.ofFn_eq_map]
    exact star_prod_comm _ _ (fun l => (model_star_c hM l).2.1) (fun i j => fc L (m_cb L i) (m_cb L j)) _
  · rw [LevelData.Dri, LevelData.Drbi, List.ofFn_eq_map, List.ofFn_eq_map]
    exact star_prod_comm _ _ (fun l => (model_star_c hM l).2.2) (fun i j => fc L (m_cbi L i) (m_cbi L j)) _

def BB (P : M.Par) (L : LevelData (MA.A P (MA.DQ P)) P.r) : Subalgebra ℂ (MA.A P (MA.DQ P)) :=
  Algebra.adjoin ℂ (MA.bddSet P L)

theorem BB_span {b : MA.A P (MA.DQ P)} (hb : b ∈ BB P L) :
    b ∈ Submodule.span ℂ (Submonoid.closure (MA.bddSet P L) : Set (MA.A P (MA.DQ P))) := by
  rw [← Algebra.adjoin_eq_span]; exact hb

theorem closure_BB {b : MA.A P (MA.DQ P)} (hb : b ∈ Submonoid.closure (MA.bddSet P L)) : b ∈ BB P L := by
  have : b ∈ Subalgebra.toSubmodule (Algebra.adjoin ℂ (MA.bddSet P L)) := by
    rw [Algebra.adjoin_eq_span]; exact Submodule.subset_span hb
  exact this

theorem model_hyp (hHB : JDHatBdd) (hTT : 0 ≤ P.TT) (hM : MA.IsModelLevel P (MA.DQ P) L) (hS : IsStarLevel L)
    (l0 : ℕ) : NFHypA L (MA.startM P (MA.DQ P) l0) (BB P L) (MA.kap P (MA.DQ P)).range := by
  have gen : ∀ {x}, x ∈ MA.bddSet P L → x ∈ BB P L := fun h => Algebra.subset_adjoin h
  have mζi : L.ζi ∈ BB P L := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have mζbi : L.ζbi ∈ BB P L := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have mDD : L.D * L.Dbi ∈ BB P L := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have mDbD : L.Db * L.Di ∈ BB P L := gen (Or.inl (Or.inl (Or.inl (by simp))))
  have mk : ∀ g, MA.kap P (MA.DQ P) g ∈ BB P L := fun g => gen (Or.inl (Or.inl (Or.inr ⟨g, rfl⟩)))
  obtain ⟨s1, s2, -⟩ := star_facts hS
  obtain ⟨d1, d2⟩ := model_star_D hM
  have s2' : star L.ζbi = L.ζi := by rw [← s2, star_star]
  have d1' : star L.Drb = L.Dr := by rw [← d1, star_star]
  have d2' : star L.Drbi = L.Dri := by rw [← d2, star_star]
  have sD : star L.D = L.Db := by
    rw [LevelData.D, star_mul, hS.1, d1, LevelData.Db, (cl_comm L (cζb L) (cDrb L)).eq]
  have sDi : star L.Di = L.Dbi := by
    rw [LevelData.Di, star_mul, s2, d2, LevelData.Dbi, (cl_comm L (cDrbi L) (cζbi L)).eq]
  have sDb : star L.Db = L.D := by rw [← sD, star_star]
  have sDbi : star L.Dbi = L.Di := by rw [← sDi, star_star]
  have hfn : ∀ b ∈ BB P L, ∀ f ∈ L.fns, Commute b f := by
    intro b hb f hf
    obtain ⟨w, hw⟩ := fns_sc hM hf
    refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hb fun x hx => ?_).symm
    have cf := clF L hf
    rcases hx with (((hx | ⟨g, rfl⟩) | ⟨i, -, rfl⟩) | ⟨i, -, rfl⟩)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact cl_comm L cf (cζi L)
      · exact cl_comm L cf (cζbi L)
      · exact cl_comm L cf (Subring.mul_mem _ (cD L) (cDbi L))
      · exact cl_comm L cf (Subring.mul_mem _ (cDb L) (cDi L))
    · rw [hw]; exact (sc_central w _ (kap_central g)).symm
    · refine (cl_comm L cf (Subring.mul_mem _ (cDrb L) (cDri L))).mul_right ?_
      rw [hw]; exact (sc_central w _ (SS_central i)).symm
    · show Commute f (star (L.Drb * L.Dri * MA.SS P (MA.DQ P) i))
      rw [star_mul, star_mul, d2, d1']
      refine Commute.mul_right ?_ (cl_comm L cf (Subring.mul_mem _ (cDrbi L) (cDr L)))
      rw [hw]
      refine (sc_central w _ fun a b => ?_).symm
      obtain ⟨z, hz⟩ := SS_central (P := P) i b a
      exact ⟨star z, by rw [Matrix.star_apply, hz, algebraMap_star_comm]⟩
  refine ⟨fun b hb => ?_, ?_, ?_, hfn, mζi, mζbi, mDD, mDbD, fun Y => ⟨_, rfl⟩, fun Y => ⟨_, rfl⟩, fun Y => ?_, ?_,
    fun X hX b hb => ?_⟩
  · induction hb using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with (((hx | ⟨g, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · rw [s2]; exact mζbi
        · rw [s2']; exact mζi
        · rw [star_mul, sD, sDbi, (cl_comm L (cDi L) (cDb L)).eq]; exact mDbD
        · rw [star_mul, sDi, sDb, (cl_comm L (cDbi L) (cD L)).eq]; exact mDD
      · rw [star_kap]; exact mk _
      · exact gen (Or.inr ⟨i, hi, rfl⟩)
      · show star (star (L.Drb * L.Dri * MA.SS P (MA.DQ P) i)) ∈ _
        rw [star_star]; exact gen (Or.inl (Or.inr ⟨i, hi, rfl⟩))
    | algebraMap c => rw [← algebraMap_star_comm]; exact Subalgebra.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [star_add]; exact Subalgebra.add_mem _ hx hy
    | mul x y _ _ hx hy => rw [star_mul]; exact Subalgebra.mul_mem _ hy hx
  · rintro b ⟨g, rfl⟩
    exact ⟨star g, (star_kap g).symm⟩
  · rintro b ⟨g, rfl⟩
    exact mk g
  · have hz := hM.2.2.2.2.2.2.1
    have hzbi := hM.2.2.2.2.2.2.2.2.2.1
    show MA.eeA P (MA.DQ P) Y ∈ _
    rw [MA.eeA, ← hz, ← hzbi, Finset.mul_sum]
    refine Subalgebra.sum_mem _ fun j hj => ?_
    have e1 : L.D * L.Dbi * (L.Drb * L.Dri) = L.ζ * L.ζbi := by
      rw [mul_assoc, ← mul_assoc L.Dbi, Dbi_Drb, LevelData.D, (cl_comm L (cDr L) (cζ L)).eq,
        (cl_comm L (cζbi L) (cDri L)).eq, mul_assoc, ← mul_assoc L.Dr, Dr_Dri, one_mul]
    rw [← mul_assoc, ← (comm_cl L (hfn _ (mk _)) (Subring.mul_mem _ (cζ L) (cζbi L))).eq, ← e1, mul_assoc,
      mul_assoc (L.D * L.Dbi)]
    exact Subalgebra.mul_mem _ (mk _) (Subalgebra.mul_mem _ mDD (gen (Or.inl (Or.inr ⟨j, Finset.mem_Icc.1 hj, rfl⟩))))
  · rintro b ⟨g, rfl⟩
    rw [hM.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
    show MA.kap P (MA.DQ P) g * MA.nabsA P (MA.DQ P) = MA.nabsA P (MA.DQ P) * MA.kap P (MA.DQ P) g
    rw [kap_diag, MA.nabsA, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext π
    exact Algebra.commutes _ _
  · have hb' := BB_span hb
    clear hb
    induction hb' using Submodule.span_induction with
    | mem b hb =>
      refine Submodule.span_le.2 ?_ (hHB P L hTT hM X hX b hb)
      rintro x ⟨b', hb', X', hX', rfl⟩
      have := nfs_one (L := L) (P := 1) (closure_BB hb') hX'
      rwa [mul_one] at this
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

theorem model_aHyp (hM : MA.IsModelLevel P (MA.DQ P) L) (hS : IsStarLevel L) {l0 : ℕ}
    (hst : IsLevelStart L (MA.startM P (MA.DQ P) l0))
    (hSi : SitesOK (K := ℂ) (MA.startM P (MA.DQ P) l0).QQ (MA.sites P (MA.DQ P))) :
    TL.AHyp L (MA.startM P (MA.DQ P) l0) := by
  refine ⟨hS, hst, fun l => (model_star_c hM l).1, fun l => (model_star_c hM l).2.1,
    fun l => (model_star_c hM l).2.2, fun Y i j x hx => ?_⟩
  have h : ∀ l, ∀ x ∈ ops (⟨L.p l, L.c l, L.ci l⟩ : Site (MA.A P (MA.DQ P))),
      Commute ((MA.startM P (MA.DQ P) l0).QQ Y i j) x := fun l => by
    have := (hSi.1 (MA.siteA P (MA.DQ P) l) (by simp [MA.sites, List.mem_ofFn])).2 Y i j
    rw [hM.1, hM.2.2.1, hM.2.2.2.1]
    exact this
  rcases hx with (((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩)
  · exact h l _ (Or.inl (Or.inl rfl))
  · have := h l (-L.pb l) (Or.inr (Or.inl (by rw [← (model_star_c hM l).1, star_star])))
    simpa using this.neg_right
  · exact h l _ (Or.inl (Or.inr (Or.inl rfl)))
  · exact h l _ (Or.inl (Or.inr (Or.inr rfl)))
  · exact h l _ (Or.inr (Or.inr (Or.inl (by rw [← (model_star_c hM l).2.1, star_star]))))
  · exact h l _ (Or.inr (Or.inr (Or.inr (by rw [← (model_star_c hM l).2.2, star_star]; rfl))))

theorem gM_eq (hM : MA.IsModelLevel P (MA.DQ P) L) (l0 : ℕ) {S : Type} [Fintype S] [DecidableEq S]
    (w : List (Letter ℂ S)) (e : Ix S) :
    gM P l0 L w e = ((ofWord L (MA.startM P (MA.DQ P) l0) w).F * TL.bTA L w) e e1 := by
  have e1 : TL.bTA L w = ((MA.sites P (MA.DQ P)).map fun σ => bT σ w).prod := by
    rw [TL.bTA, hM.1, hM.2.2.1, hM.2.2.2.1]
    simp [MA.sites, List.ofFn_eq_map, List.map_reverse, Function.comp_def, MA.siteA]
  rw [e1, Matrix.mul_apply]
  rfl

theorem nfs_fin {Q x : MA.A P (MA.DQ P)} {n : ℕ} (hx : x ∈ NFs L (BB P L) Q n) :
    ∃ (m : ℕ) (b : Fin m → MA.A P (MA.DQ P)) (u : Fin m → List (MA.A P (MA.DQ P))),
      (∀ j, b j ∈ Submonoid.closure (MA.bddSet P L)) ∧ (∀ j, (u j).length = n ∧ ∀ a ∈ u j, a ∈ MA.hatSet P L) ∧
      x = ∑ j, b j * Q * (u j).prod := by
  have h1 : x ∈ Submodule.span ℂ {x | ∃ b ∈ Submonoid.closure (MA.bddSet P L), ∃ h : List (MA.A P (MA.DQ P)),
      h.length = n ∧ (∀ a ∈ h, a ∈ hats L) ∧ x = b * Q * h.prod} := by
    refine Submodule.span_le.2 ?_ hx
    rintro y ⟨b, hb, h, hl, hh, rfl⟩
    have hb' := BB_span hb
    clear hb
    induction hb' using Submodule.span_induction with
    | mem b hb => exact Submodule.subset_span ⟨b, hb, h, hl, hh, rfl⟩
    | zero => rw [zero_mul, zero_mul]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [add_mul, add_mul]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [smul_mul_assoc, smul_mul_assoc]; exact Submodule.smul_mem _ _ hx
  obtain ⟨m, c, g, hs⟩ := Submodule.mem_span_set'.1 h1
  choose b hb u hl hh hg using fun j => (g j).2
  refine ⟨m, fun j => MA.kap P (MA.DQ P) (fun _ => c j) * b j, u,
    fun j => Submonoid.mul_mem _ (jdh_kap_mem P L _) (hb j), fun j => ⟨hl j, hh j⟩, ?_⟩
  rw [← hs]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hg j, jdh_smul_eq]
  simp only [mul_assoc]

def MulBy (a : MA.A P (MA.DQ P)) (φ : MA.Qp P.r P.TT → ℂ) : Prop :=
  ∀ f ρ q, MA.evQ P (MA.actA P a f ρ) q = φ q * MA.evQ P (f ρ) q

theorem MulBy.mul {a b : MA.A P (MA.DQ P)} {φ ψ} (ha : MulBy a φ) (hb : MulBy b ψ) :
    MulBy (a * b) fun q => φ q * ψ q := fun f ρ q => by rw [Gauge.actA_mul, ha, hb, mul_assoc]

theorem mulBy_one : MulBy (1 : MA.A P (MA.DQ P)) fun _ => 1 := fun f ρ q => by rw [jdh_actA_one, one_mul]

theorem MulBy.pow {a : MA.A P (MA.DQ P)} {φ} (ha : MulBy a φ) (n : ℕ) : MulBy (a ^ n) fun q => φ q ^ n := by
  induction n with
  | zero => simpa using mulBy_one
  | succ n ih => simpa only [pow_succ] using ih.mul ha

theorem mulBy_prod {ι : Type} (a : ι → MA.A P (MA.DQ P)) (φ : ι → MA.Qp P.r P.TT → ℂ) (h : ∀ i, MulBy (a i) (φ i))
    (l : List ι) : MulBy (l.map a).prod fun q => (l.map fun i => φ i q).prod := by
  induction l with
  | nil => simpa using mulBy_one
  | cons i l ih => simpa only [List.map_cons, List.prod_cons] using (h i).mul ih

theorem MulBy.inv {a b : MA.A P (MA.DQ P)} {φ} (ha : MulBy a φ) (h : a * b = 1) (h0 : ∀ q, φ q ≠ 0) :
    MulBy b fun q => (φ q)⁻¹ := fun f ρ q => by
  have := ha (MA.actA P b f) ρ q
  rw [← Gauge.actA_mul, h, jdh_actA_one] at this
  rw [this, ← mul_assoc, inv_mul_cancel₀ (h0 q), one_mul]

theorem mulBy_fn (g gb : MA.SmQ P.r P.TT) : MulBy (MA.sc P (MA.DQ P) ((MA.DQ P).fnP g gb)) (MA.evQ P g) :=
  fun f ρ q => by rw [act_sc]; rfl

theorem MulBy.congr {a : MA.A P (MA.DQ P)} {φ ψ} (ha : MulBy a φ) (h : ∀ q, ψ q = φ q) : MulBy a ψ := by
  rw [funext h]; exact ha

theorem mulBy_D (hM : MA.IsModelLevel P (MA.DQ P) L) : MulBy L.D (fun q => (∏ l, q.1.1 l) * q.1.2) ∧
    MulBy L.G fun q => ((MA.Gq P q : ℝ) : ℂ) := by
  obtain ⟨-, -, hc, -, hcb, -, hz, -, -, -, hg, -⟩ := hM
  have h1 : ∀ l, MulBy (L.c l) fun q => q.1.1 l := fun l => by
    rw [hc]
    refine (mulBy_fn (P := P) (MA.coordQ (M.vc l)) (MA.coordQ (M.vcb l))).congr fun q => ?_
    simp [MA.evQ, MA.coordQ, MA.coordE, MA.zE, M.vc]
  have h2 : ∀ l, MulBy (L.cb l) fun q => star (q.1.1 l) := fun l => by
    rw [hcb]
    refine (mulBy_fn (P := P) (MA.coordQ (M.vcb l)) (MA.coordQ (M.vc l))).congr fun q => ?_
    simp [MA.evQ, MA.coordQ, MA.coordE, MA.zE, M.vcb]
  have h3 : MulBy L.ζ fun q => q.1.2 := by
    rw [hz]
    refine (mulBy_fn (P := P) (MA.coordQ M.vz) (MA.coordQ M.vzb)).congr fun q => ?_
    simp [MA.evQ, MA.coordQ, MA.coordE, MA.zE, M.vz]
  have h4 : MulBy L.GG fun q => ((Complex.normSq q.1.2 - P.TT : ℝ) : ℂ) := by
    rw [hg]
    refine (mulBy_fn (P := P) ((MA.DQ P).gg P.TT) ((MA.DQ P).gg P.TT)).congr fun q => ?_
    show _ = MA.coordE M.vz q.1 * MA.coordE M.vzb q.1 - (P.TT : ℂ)
    simp [MA.coordE, MA.zE, M.vz, M.vzb, Complex.mul_conj]
  have hDr : MulBy L.Dr fun q => ∏ l, q.1.1 l := by
    have := mulBy_prod L.c _ h1 (List.finRange P.r)
    rw [LevelData.Dr, List.ofFn_eq_map]
    simpa only [Fin.prod_univ_def] using this
  have hDrb : MulBy L.Drb fun q => ∏ l, star (q.1.1 l) := by
    have := mulBy_prod L.cb _ h2 (List.finRange P.r)
    rw [LevelData.Drb, List.ofFn_eq_map]
    simpa only [Fin.prod_univ_def] using this
  refine ⟨hDr.mul h3, ?_⟩
  refine ((hDr.mul hDrb).mul h4).congr fun q => ?_
  rw [MA.Gq, ← Finset.prod_mul_distrib, Complex.ofReal_mul, Complex.ofReal_prod]
  simp [Complex.mul_conj]

theorem nf_pointwise (hTT : 0 ≤ P.TT) (hM : MA.IsModelLevel P (MA.DQ P) L)
    (hfn : ∀ b ∈ BB P L, ∀ f ∈ L.fns, Commute b f) {x : MA.A P (MA.DQ P)} {n : ℕ}
    (hx : x ∈ NFs L (BB P L) (L.Di ^ n) n) (s : ℕ) :
    ∃ (m : ℕ) (b : Fin m → MA.A P (MA.DQ P)) (u : Fin m → List (MA.A P (MA.DQ P))),
      (∀ j, b j ∈ Submonoid.closure (MA.bddSet P L)) ∧ (∀ j, (u j).length = n ∧ ∀ a ∈ u j, a ∈ MA.hatSet P L) ∧
      ∀ f g : M.Ty P → MA.SmQ P.r P.TT,
        (∀ ρ q, MA.evQ P (g ρ) q = ((MA.Gq P q ^ s : ℝ) : ℂ) * MA.evQ P (f ρ) q) → ∀ (q : MA.Qp P.r P.TT) ρ,
        MA.evQ P (MA.actA P x g ρ) q = ((MA.Gq P q ^ s : ℝ) : ℂ) * ((∏ l, q.1.1 l) * q.1.2)⁻¹ ^ n *
          ∑ j, MA.evQ P (MA.actA P (b j * (u j).prod) f ρ) q := by
  obtain ⟨m, b, u, hb, hu, rfl⟩ := nfs_fin hx
  choose u' hl hh he using fun j => hats_Gpow L s (u j) (hu j).2
  refine ⟨m, b, u', hb, fun j => ⟨(hl j).trans (hu j).1, hh j⟩, fun f g hg q ρ => ?_⟩
  obtain ⟨hD, hG⟩ := mulBy_D hM
  have hDi := hD.inv (D_Di L) fun q => mul_ne_zero (Finset.prod_ne_zero_iff.2 fun l _ => q.2.1 l) (by
    intro h0
    have := q.2.2
    rw [h0, map_zero] at this
    exact absurd hTT (not_le.2 this))
  have eg : g = MA.actA P (L.G ^ s) f := by
    funext ρ'
    apply Subtype.ext
    funext q'
    have := hG.pow s f ρ' q'
    beta_reduce at this
    rw [← Complex.ofReal_pow, ← hg] at this
    exact this.symm
  have ex : (∑ j, b j * L.Di ^ n * (u j).prod) * L.G ^ s = L.G ^ s * L.Di ^ n * ∑ j, b j * (u' j).prod := by
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have c1 := ((comm_cl L (hfn _ (closure_BB (hb j))) (cDi L)).pow_right n).eq
    have c2 := ((comm_cl L (hfn _ (closure_BB (hb j))) (cG L)).pow_right s).eq
    have c3 := ((cl_comm L (cDi L) (cG L)).pow_pow n s).eq
    rw [mul_assoc, he j, c1]
    calc L.Di ^ n * b j * (L.G ^ s * (u' j).prod) = L.Di ^ n * (b j * L.G ^ s) * (u' j).prod := by
          simp only [mul_assoc]
      _ = (L.Di ^ n * L.G ^ s) * (b j * (u' j).prod) := by rw [c2]; simp only [mul_assoc]
      _ = _ := by rw [c3]
  rw [eg, ← Gauge.actA_mul, ex, Gauge.actA_mul, ((hG.pow s).mul (hDi.pow n)), Gauge.actA_sum, Finset.sum_apply,
    Complex.ofReal_pow]
  congr 1
  simp only [MA.evQ, AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]

end model

end

end Formalism.FourierDecayAlt.P.NormalFormRelations
